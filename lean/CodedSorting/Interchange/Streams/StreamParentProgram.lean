import CodedSorting.Interchange.Local.PartialSwapExecution
import CodedSorting.Interchange.Bounds.ExchangeInterface

section StreamSplitLayoutCore
/-! Generic physical address boundaries for the Construction split. No old network
dimension, old stream count or old radix appears in these definitions.
This pure layout file does not supply a machine program. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.Construction.StreamSplitLayout

open Address CoordinateScans SingleCoordinate CommonAddressLayout
open PartialSwapScan PartialSwapExecution TriangularStreams
open ScanProgram

noncomputable section

section CyclicPass

def transposeTriples (rows W L : ℕ) : TripleAddress rows W L ≃ TripleAddress W rows L where
  toFun a := (a.2.1,a.1,a.2.2)
  invFun a := (a.2.1,a.1,a.2.2)
  left_inv a := by rcases a with ⟨r,c,z⟩; rfl
  right_inv a := by rcases a with ⟨c,r,z⟩; rfl

theorem transposeCard (rows W L : ℕ) : W*(rows*L) = rows*(W*L) := by ring

def cyclicPermutation (rows W L : ℕ) : Equiv.Perm (Fin (rows*(W*L))) :=
  tripleEncode.symm.trans ((transposeTriples rows W L).trans
    (tripleEncode.trans (finCongr (transposeCard rows W L))))

def cyclicKey (rows W L : ℕ) (x : Fin (rows*(W*L))) : Fin W :=
  (tripleEncode.symm x).2.1

theorem cyclic_encoded (rows W L : ℕ) (r : Fin rows) (c : Fin W) (z : Fin L) :
    cyclicPermutation rows W L (tripleEncode (r,c,z)) =
      finCongr (transposeCard rows W L) (tripleEncode (c,r,z)) := by
  simp only [cyclicPermutation,Equiv.trans_apply,Equiv.symm_apply_apply,transposeTriples,
    Equiv.coe_fn_mk]

theorem cyclic_increasing (rows W L : ℕ) :
    ∀ x y, x < y → cyclicKey rows W L x = cyclicKey rows W L y →
      cyclicPermutation rows W L x < cyclicPermutation rows W L y := by
  intro x y hxy hk
  obtain ⟨⟨r,c,z⟩,rfl⟩ := tripleEncode.surjective x
  obtain ⟨⟨r',c',z'⟩,rfl⟩ := tripleEncode.surjective y
  simp only [cyclicKey,Equiv.symm_apply_apply] at hk
  subst c'
  rw [cyclic_encoded,cyclic_encoded]
  change tripleEncode (c,r,z) < tripleEncode (c,r',z')
  apply (tripleEncode_lt_iff _ _).mpr
  rcases (tripleEncode_lt_iff _ _).mp hxy with hr | ⟨hr,hc | ⟨_,hz⟩⟩
  · exact Or.inr ⟨rfl,Or.inl hr⟩
  · exact (lt_irrefl c hc).elim
  · exact Or.inr ⟨rfl,Or.inr ⟨hr,hz⟩⟩

/-- This is a charged stable distribution, not an address regrouping.
The W streams are shared by all prefix rows. -/
def rawSplitPass (rows W L : ℕ) : Pass (rows*(W*L)) :=
  .streams W (cyclicPermutation rows W L) (cyclicKey rows W L) (cyclic_increasing rows W L)

def gatherKey (rows W L : ℕ) (x : Fin (rows*(W*L))) : Fin W :=
  (tripleEncode.symm ((finCongr (transposeCard rows W L)).symm x)).1

theorem gather_encoded (rows W L : ℕ) (r : Fin rows) (c : Fin W) (z : Fin L) :
    (cyclicPermutation rows W L).symm
      (finCongr (transposeCard rows W L) (tripleEncode (c,r,z))) = tripleEncode (r,c,z) := by
  rw [←cyclic_encoded,Equiv.symm_apply_apply]

theorem gather_increasing (rows W L : ℕ) :
    ∀ x y, x < y → gatherKey rows W L x = gatherKey rows W L y →
      (cyclicPermutation rows W L).symm x < (cyclicPermutation rows W L).symm y := by
  intro x y hxy hk
  obtain ⟨x,rfl⟩ := (finCongr (transposeCard rows W L)).surjective x
  obtain ⟨y,rfl⟩ := (finCongr (transposeCard rows W L)).surjective y
  obtain ⟨⟨c,r,z⟩,rfl⟩ := tripleEncode.surjective x
  obtain ⟨⟨c',r',z'⟩,rfl⟩ := tripleEncode.surjective y
  simp only [gatherKey,Equiv.symm_apply_apply] at hk
  subst c'
  change tripleEncode (c,r,z) < tripleEncode (c,r',z') at hxy
  rw [gather_encoded,gather_encoded]
  apply (tripleEncode_lt_iff _ _).mpr
  rcases (tripleEncode_lt_iff _ _).mp hxy with hc | ⟨_,hr | ⟨hr,hz⟩⟩
  · exact (lt_irrefl c hc).elim
  · exact Or.inl hr
  · exact Or.inr ⟨hr,Or.inr ⟨rfl,hz⟩⟩

/-- Gathering also uses W shared streams, independent of the row count. -/
def rawGatherPass (rows W L : ℕ) : Pass (rows*(W*L)) :=
  .streams W (cyclicPermutation rows W L).symm (gatherKey rows W L)
    (gather_increasing rows W L)

end CyclicPass

section Distribution
variable {m Q rows W G S : ℕ}

abbrev SegmentCount (m Q G S : ℕ) := (FieldCount (Fin m) Q*G)*(FieldCount (Fin m) Q*S)

def bodyCode {Pref : ℕ} (a : Addr (Fin m) Pref Q G S) : Fin (SegmentCount m Q G S) :=
  finProdFinEquiv (finProdFinEquiv (LexBlocks.subvectorEncode a.high,a.gap),
    finProdFinEquiv (LexBlocks.subvectorEncode a.low,a.suffix))

def parentAddress (c : Fin W) (a : Addr (Fin m) rows Q G S) : Addr (Fin m) (rows*W) Q G S :=
  ⟨finProdFinEquiv (a.prefixCoord,c),a.high,a.gap,a.low,a.suffix⟩

theorem parentAddress_surjective (a : Addr (Fin m) (rows*W) Q G S) :
    ∃ c : Fin W, ∃ b : Addr (Fin m) rows Q G S, parentAddress c b=a := by
  rcases a with ⟨p,h,g,l,s⟩
  obtain ⟨⟨r,c⟩,rfl⟩ := finProdFinEquiv.surjective p
  exact ⟨c,⟨r,h,g,l,s⟩,rfl⟩

theorem parentAddress_exchange (c : Fin W) (a : Addr (Fin m) rows Q G S) :
    parentAddress c (exchange a)=exchange (parentAddress c a) := rfl

theorem distributionVolume (m Q rows W G S : ℕ) :
    rows*(W*SegmentCount m Q G S) = Volume (Fin m) (rows*W) Q G S := by
  unfold SegmentCount Volume
  ring

theorem streamVolume (m Q rows W G S : ℕ) :
    W*Volume (Fin m) rows Q G S = Volume (Fin m) (rows*W) Q G S := by
  unfold Volume
  ring

theorem parent_triples (c : Fin W) (a : Addr (Fin m) rows Q G S) :
    longLayout (parentAddress c a) = finCongr (distributionVolume m Q rows W G S)
      (tripleEncode (a.prefixCoord,c,bodyCode a)) := by
  apply Fin.ext
  simp only [longLayout_val,parentAddress,finCongr_apply_coe,tripleEncode_val,bodyCode,
    finProdFinEquiv,Equiv.coe_fn_mk,SegmentCount]
  ring

theorem stream_triples (c : Fin W) (a : Addr (Fin m) rows Q G S) :
    finCongr (streamVolume m Q rows W G S) (finProdFinEquiv (c,longLayout a)) =
      finCongr (distributionVolume m Q rows W G S)
        (finCongr (transposeCard rows W (SegmentCount m Q G S))
          (tripleEncode (c,a.prefixCoord,bodyCode a))) := by
  apply Fin.ext
  simp only [longLayout_val,finCongr_apply_coe,tripleEncode_val,bodyCode,
    finProdFinEquiv,Equiv.coe_fn_mk,SegmentCount,Volume]
  ring

def splitPass (m Q rows W G S : ℕ) : Pass (Volume (Fin m) (rows*W) Q G S) :=
  castPass (distributionVolume m Q rows W G S) (rawSplitPass rows W (SegmentCount m Q G S))

def gatherPass (m Q rows W G S : ℕ) : Pass (Volume (Fin m) (rows*W) Q G S) :=
  castPass (distributionVolume m Q rows W G S) (rawGatherPass rows W (SegmentCount m Q G S))

theorem splitPass_encoded (c : Fin W) (a : Addr (Fin m) rows Q G S) :
    (splitPass m Q rows W G S).permutation (longLayout (parentAddress c a)) =
      finCongr (streamVolume m Q rows W G S) (finProdFinEquiv (c,longLayout a)) := by
  rw [parent_triples,splitPass,castPass_encoded]
  change finCongr _ (cyclicPermutation rows W _ (tripleEncode _)) = _
  rw [cyclic_encoded,←stream_triples]

theorem gatherPass_encoded (c : Fin W) (a : Addr (Fin m) rows Q G S) :
    (gatherPass m Q rows W G S).permutation
      (finCongr (streamVolume m Q rows W G S) (finProdFinEquiv (c,longLayout a))) =
        longLayout (parentAddress c a) := by
  rw [stream_triples,gatherPass,castPass_encoded]
  change finCongr _ ((cyclicPermutation rows W _).symm (finCongr _ (tripleEncode _))) = _
  rw [gather_encoded,←parent_triples]

theorem splitPass_constant (m Q rows W G S : ℕ) : (splitPass m Q rows W G S).constant = 2*W+6 := by
  rw [splitPass,castPass_constant]
  rfl

theorem gatherPass_constant (m Q rows W G S : ℕ) : (gatherPass m Q rows W G S).constant = 2*W+6 := by
  rw [gatherPass,castPass_constant]
  rfl

theorem splitPass_execution {Value : Type*} [Inhabited Value]
    (m Q rows W G S : ℕ) (input : Fin (Volume (Fin m) (rows*W) Q G S) → Value)
    (B : ℕ) (hb : 0 < B) :
    ∃ cost, StepEvidence (splitPass m Q rows W G S) input B hb cost ∧
      cost ≤ (2*W+6)*(Volume (Fin m) (rows*W) Q G S/B+1) := by
  simpa only [splitPass_constant] using pass_correct (splitPass m Q rows W G S) input B hb

theorem gatherPass_execution {Value : Type*} [Inhabited Value]
    (m Q rows W G S : ℕ) (input : Fin (Volume (Fin m) (rows*W) Q G S) → Value)
    (B : ℕ) (hb : 0 < B) :
    ∃ cost, StepEvidence (gatherPass m Q rows W G S) input B hb cost ∧
      cost ≤ (2*W+6)*(Volume (Fin m) (rows*W) Q G S/B+1) := by
  simpa only [gatherPass_constant] using pass_correct (gatherPass m Q rows W G S) input B hb

end Distribution

abbrev ScalarVolume (radix width Pref G S : ℕ) :=
  (Pref*(radix^width*G))*(radix^width*S)

theorem packedPower (radix m f : ℕ) : (radix^f)^m = radix^(m*f) := by
  rw [←pow_mul,Nat.mul_comm f m]

def packedField (radix m f : ℕ) : (Fin m → Fin (radix^f)) ≃ Fin (radix^(m*f)) :=
  lexLayout.trans (finCongr (packedPower radix m f))

theorem packedVolume (radix m f Pref G S : ℕ) :
    ScalarVolume radix (m*f) Pref G S = Volume (Fin m) Pref (radix^f) G S := by
  simp only [ScalarVolume,Volume,FieldCount,Fintype.card_fin,←packedPower]

theorem packed_same_address (radix m f Pref G S : ℕ)
    (a : Addr (Fin m) Pref (radix^f) G S) :
    finCongr (packedVolume radix m f Pref G S)
      (lowLayout (FieldPacking.fieldEquiv (packedField radix m f) a)) = longLayout a := by
  apply Fin.ext
  simp only [finCongr_apply_coe,lowLayout_val,FieldPacking.fieldEquiv,
    Equiv.coe_fn_mk,packedField,Equiv.trans_apply,longLayout_val,
    vector_code_val,FieldCount,Fintype.card_fin,←packedPower]

theorem packed_exchange (radix m f Pref G S : ℕ)
    (a : Addr (Fin m) Pref (radix^f) G S) :
    FieldPacking.fieldEquiv (packedField radix m f) (exchange a)=
      exchange (FieldPacking.fieldEquiv (packedField radix m f) a) := rfl

def selectedRepack {m Q Pref G S : ℕ} (i j : Fin m) :
    Addr (Fin m) Pref Q G S ≃
      FullAddress (Fin (ChildPrefix Pref Q i)) (Fin Q)
        (Fin (ChildGap G Q i j)) (Fin (ChildSuffix S Q j)) :=
  (repack i j).trans (childShape i j)

theorem selected_same_address {m Q Pref G S : ℕ} (i j : Fin m)
    (a : Addr (Fin m) Pref Q G S) :
    finCongr (childVolume (P := Pref) (G := G) (S := S) (Q := Q) i j)
      (lowLayout (selectedRepack i j a)) = longLayout a :=
  childLayout_repack i j a

theorem selected_exchange {m Q Pref G S : ℕ} (i j : Fin m)
    (a : Addr (Fin m) Pref Q G S) :
    selectedRepack i j (shortExchange i j a) = exchange (selectedRepack i j a) := by
  exact selected_encoded i j (Equiv.prodComm (Fin Q) (Fin Q)) a


end
end CodedSorting.Construction.StreamSplitLayout
end StreamSplitLayoutCore

section StreamSplitLayout
/-! Actual recursive-call adapters for the generic Construction stream layout.
The layout itself is independent of the old concrete machine network. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.Construction.StreamSplitLayout

open Address CoordinateScans SingleCoordinate CommonAddressLayout
open PartialSwapScan PartialSwapExecution TriangularStreams
open ScanProgram
noncomputable section

theorem packed_swap_encoded (radix m f Pref G S : ℕ)
    (a : Addr (Fin m) Pref (radix^f) G S) :
    finCongr (packedVolume radix m f Pref G S)
      (CommonChunkLayout.swap Pref (radix^(m*f)) G S
        (lowLayout (FieldPacking.fieldEquiv (packedField radix m f) a))) =
      longLayout (exchange a) := by
  rw [CommonChunkLayout.swap_encoded,←packed_exchange]
  exact packed_same_address radix m f Pref G S (exchange a)

/-- The full bank exchange is exactly the scalar parent exchange under the
same-address packing. This cast introduces no pass or hidden permutation. -/
theorem packed_permutation (radix m f Pref G S : ℕ) :
    (finCongr (packedVolume radix m f Pref G S)).symm.trans
      ((CommonChunkLayout.swap Pref (radix^(m*f)) G S).trans
        (finCongr (packedVolume radix m f Pref G S))) =
      longLayout.symm.trans (exchangeEquiv.trans longLayout) := by
  apply Equiv.ext
  intro x
  obtain ⟨a,rfl⟩ := (longLayout (I := Fin m) (P := Pref) (Q := radix^f)
    (G := G) (S := S)).surjective x
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
  change finCongr _ (CommonChunkLayout.swap _ _ _ _ ((finCongr _).symm (longLayout a))) =
    longLayout (exchange a)
  rw [←packed_same_address radix m f Pref G S a,Equiv.symm_apply_apply]
  exact packed_swap_encoded radix m f Pref G S a

theorem selected_swap_encoded {m Q Pref G S : ℕ} (i j : Fin m)
    (a : Addr (Fin m) Pref Q G S) :
    finCongr (childVolume (P := Pref) (G := G) (S := S) (Q := Q) i j)
      (CommonChunkLayout.swap (ChildPrefix Pref Q i) Q (ChildGap G Q i j) (ChildSuffix S Q j)
        (lowLayout (selectedRepack i j a))) = longLayout (shortExchange i j a) := by
  rw [CommonChunkLayout.swap_encoded,←selected_exchange]
  exact selected_same_address i j (shortExchange i j a)

/-- The ordinary numeric scalar-child permutation, cast only along an exact
volume equality, is the selected swap on the original mixed-layout file. -/
theorem selected_permutation {m Q Pref G S : ℕ} (i j : Fin m) :
    (finCongr (childVolume (P := Pref) (G := G) (S := S) (Q := Q) i j)).symm.trans
      ((CommonChunkLayout.swap (ChildPrefix Pref Q i) Q (ChildGap G Q i j)
        (ChildSuffix S Q j)).trans (finCongr (childVolume i j))) =
      longLayout.symm.trans ((shortExchange i j).trans longLayout) := by
  apply Equiv.ext
  intro x
  obtain ⟨a,rfl⟩ := (longLayout (I := Fin m) (P := Pref) (Q := Q) (G := G) (S := S)).surjective x
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
  change finCongr _ (CommonChunkLayout.swap _ _ _ _ ((finCongr _).symm (longLayout a))) =
    longLayout (shortExchange i j a)
  rw [←selected_same_address i j a,Equiv.symm_apply_apply]
  exact selected_swap_encoded i j a


def selectedCall (radix m f Pref G S : ℕ) (i j : Fin m)
    (source buffer limit : ℕ) : ExchangeInterface.Call :=
  ⟨f,ChildPrefix Pref (radix^f) i,ChildGap G (radix^f) i j,
    ChildSuffix S (radix^f) j,source,buffer,limit⟩

theorem selectedCall_volume (radix m f Pref G S : ℕ) (i j : Fin m)
    (source buffer limit : ℕ) :
    ExchangeInterface.volume radix (selectedCall radix m f Pref G S i j source buffer limit) =
      Volume (Fin m) Pref (radix^f) G S := childVolume i j

theorem parent_volume (radix m f rows W G S : ℕ) :
    ScalarVolume radix (m*f) (rows*W) G S =
      W*Volume (Fin m) rows (radix^f) G S := by
  rw [packedVolume]
  unfold Volume
  ring

theorem selected_volume_div (radix m f rows W G S : ℕ) (hW : 0 < W)
    (i j : Fin m) (source buffer limit : ℕ) :
    ExchangeInterface.volume radix (selectedCall radix m f rows G S i j source buffer limit) =
      ScalarVolume radix (m*f) (rows*W) G S / W := by
  rw [selectedCall_volume,parent_volume,Nat.mul_div_cancel_left _ hW]

/-- Selection multiplies the lane prefix by the earlier high coordinates.
It does not consume another stream-count factor. -/
theorem selected_prefix_power (m Q rows W k : ℕ) (i : Fin m) :
    ChildPrefix (rows*W^k) Q i = (rows*BeforeCount Q i)*W^k := by
  unfold ChildPrefix
  ring

theorem selected_prefix_divisible (m Q rows W k : ℕ) (i : Fin m) :
    W^k ∣ ChildPrefix (rows*W^k) Q i := by
  rw [selected_prefix_power]
  exact dvd_mul_left _ _

theorem prefix_after_split (m Q Pref W k : ℕ) (hW : 0 < W)
    (hp : W^(k+1) ∣ Pref) (i : Fin m) : W^k ∣ ChildPrefix (Pref/W) Q i := by
  obtain ⟨rows,hr⟩ := hp
  have he : Pref/W = rows*W^k := by
    rw [hr,pow_succ]
    have hmul : W^k*W*rows = (rows*W^k)*W := by ring
    rw [hmul,Nat.mul_div_cancel _ hW]
  rw [he]
  exact selected_prefix_divisible m Q rows W k i

theorem e8_selected_volume_div (radix f rows G S : ℕ)
    (i j : Fin ambientDimension) (source buffer limit : ℕ) :
    ExchangeInterface.volume radix
      (selectedCall radix ambientDimension f rows G S i j source buffer limit) =
      ScalarVolume radix (ambientDimension*f) (rows*streamCount) G S / streamCount :=
  selected_volume_div radix ambientDimension f rows streamCount G S
    (by decide) i j source buffer limit


/-- Reinterpret the actual scalar child at its identical physical bit addresses.
No instructions, auxiliary storage or charge are introduced by regrouping. -/
def selectedChildProgram (q : CommonSortingNormalization.Configuration)
    (radix m f Pref G S : ℕ) (i j : Fin m) (source buffer limit : ℕ)
    (child : ExchangeInterface.Program q radix
      (selectedCall radix m f Pref G S i j source buffer limit)) :
    CommonFinitePermutation.Program q (Volume (Fin m) Pref (radix^f) G S)
      source buffer limit
      (longLayout.symm.trans ((shortExchange i j).trans longLayout)) :=
  let p := child.castVolume (selectedCall_volume radix m f Pref G S i j source buffer limit)
  { instructions := p.instructions
    charge := p.charge
    correct := by
      intro state y
      rw [←selected_permutation i j]
      exact p.correct state y
    frame := p.frame
    safe := p.safe
    cost_le := p.cost_le
    length_le := p.length_le }

theorem selectedChildProgram_instructions (q : CommonSortingNormalization.Configuration)
    (radix m f Pref G S : ℕ) (i j : Fin m) (source buffer limit : ℕ)
    (child : ExchangeInterface.Program q radix
      (selectedCall radix m f Pref G S i j source buffer limit)) :
    (selectedChildProgram q radix m f Pref G S i j source buffer limit child).instructions =
      child.instructions := rfl

theorem selectedChildProgram_charge (q : CommonSortingNormalization.Configuration)
    (radix m f Pref G S : ℕ) (i j : Fin m) (source buffer limit : ℕ)
    (child : ExchangeInterface.Program q radix
      (selectedCall radix m f Pref G S i j source buffer limit)) :
    (selectedChildProgram q radix m f Pref G S i j source buffer limit child).charge =
      child.charge := rfl

end
end CodedSorting.Construction.StreamSplitLayout

#print axioms CodedSorting.Construction.StreamSplitLayout.selectedChildProgram
end StreamSplitLayout

section StreamSplitMachine
/-!
# Actual split and gather instructions for selected Construction sessions

The stable transpose is a charged machine scan. The subsequent slab split
copies exactly the selected independent sessions into arbitrary allocated
network slots; temporary registers are not added to the session count.
Gather performs the inverse two actual scans. All payload equations below
refer to `executeRaw` of the displayed instruction lists.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace CodedSorting.Construction.StreamSplitMachine

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine Disk)
open CoordinateScans CommonAddressLayout ScanProgram PhysicalStreamCursor PartialSwapScan
open StreamSplitLayout
noncomputable section

section Transpose
variable (q : Configuration) (reader : Fin q.inventory.readers)
variable (m Q rows W G S source target : ℕ)

/-- Actual stable distribution from row-major parent positions to session-major positions. -/
def transposeCode : List (Instruction q) :=
  CommonScanProgram.passCode q reader (splitPass m Q rows W G S) source target

/-- Actual inverse stable distribution, with the same `W` stream count. -/
def inverseCode : List (Instruction q) :=
  CommonScanProgram.passCode q reader (gatherPass m Q rows W G S) source target

theorem transpose_safe : ∀ i ∈ transposeCode q reader m Q rows W G S source target,
    RespectsPC q i := CommonScanProgram.pass_safe q reader _ source target

theorem inverse_safe : ∀ i ∈ inverseCode q reader m Q rows W G S source target,
    RespectsPC q i := CommonScanProgram.pass_safe q reader _ source target

theorem transpose_cost : cost q (transposeCode q reader m Q rows W G S source target) ≤
    3*(2*W+6)*count q (Volume (Fin m) (rows*W) Q G S) := by
  simpa only [splitPass_constant] using
    CommonScanProgram.pass_cost q reader (splitPass m Q rows W G S) source target

theorem transpose_length : (transposeCode q reader m Q rows W G S source target).length ≤
    3*(2*W+6)*count q (Volume (Fin m) (rows*W) Q G S) := by
  simpa only [splitPass_constant] using
    CommonScanProgram.pass_length q reader (splitPass m Q rows W G S) source target

theorem inverse_cost : cost q (inverseCode q reader m Q rows W G S source target) ≤
    3*(2*W+6)*count q (Volume (Fin m) (rows*W) Q G S) := by
  simpa only [gatherPass_constant] using
    CommonScanProgram.pass_cost q reader (gatherPass m Q rows W G S) source target

theorem inverse_length : (inverseCode q reader m Q rows W G S source target).length ≤
    3*(2*W+6)*count q (Volume (Fin m) (rows*W) Q G S) := by
  simpa only [gatherPass_constant] using
    CommonScanProgram.pass_length q reader (gatherPass m Q rows W G S) source target

theorem transpose_raw (s : Machine q)
    (hsource : source+count q (Volume (Fin m) (rows*W) Q G S) ≤ q.N^q.exponent)
    (htarget : target+count q (Volume (Fin m) (rows*W) Q G S) ≤ q.N^q.exponent)
    (hsep : source+count q (Volume (Fin m) (rows*W) Q G S) ≤ target ∨
      target+count q (Volume (Fin m) (rows*W) Q G S) ≤ source)
    (c : Fin W) (a : Addr (Fin m) rows Q G S) :
    readBit q (executeRaw q (transposeCode q reader m Q rows W G S source target) s).1.disk
      target (c.val*Volume (Fin m) rows Q G S+(longLayout a).val) =
      readBit q s.disk source (longLayout (parentAddress c a)).val := by
  have h := (CommonScanProgram.pass_raw q reader (splitPass m Q rows W G S)
    source target s hsource htarget hsep).1
      ((splitPass m Q rows W G S).permutation (longLayout (parentAddress c a)))
  rw [Equiv.symm_apply_apply,splitPass_encoded] at h
  simpa only [finCongr_apply_coe,BitWordPacking.bit_address] using h

theorem inverse_raw (s : Machine q)
    (hsource : source+count q (Volume (Fin m) (rows*W) Q G S) ≤ q.N^q.exponent)
    (htarget : target+count q (Volume (Fin m) (rows*W) Q G S) ≤ q.N^q.exponent)
    (hsep : source+count q (Volume (Fin m) (rows*W) Q G S) ≤ target ∨
      target+count q (Volume (Fin m) (rows*W) Q G S) ≤ source)
    (c : Fin W) (a : Addr (Fin m) rows Q G S) :
    readBit q (executeRaw q (inverseCode q reader m Q rows W G S source target) s).1.disk
      target (longLayout (parentAddress c a)).val =
      readBit q s.disk source (c.val*Volume (Fin m) rows Q G S+(longLayout a).val) := by
  have h := (CommonScanProgram.pass_raw q reader (gatherPass m Q rows W G S)
    source target s hsource htarget hsep).1
      ((gatherPass m Q rows W G S).permutation
        (finCongr (streamVolume m Q rows W G S) (finProdFinEquiv (c,longLayout a))))
  rw [Equiv.symm_apply_apply,gatherPass_encoded] at h
  simpa only [finCongr_apply_coe,BitWordPacking.bit_address] using h

theorem transpose_outside (s : Machine q)
    (hsource : source+count q (Volume (Fin m) (rows*W) Q G S) ≤ q.N^q.exponent)
    (htarget : target+count q (Volume (Fin m) (rows*W) Q G S) ≤ q.N^q.exponent)
    (hsep : source+count q (Volume (Fin m) (rows*W) Q G S) ≤ target ∨
      target+count q (Volume (Fin m) (rows*W) Q G S) ≤ source)
    (a : Fin (q.N^q.exponent))
    (ha : a.val<target ∨ target+count q (Volume (Fin m) (rows*W) Q G S)≤a.val) :
    (executeRaw q (transposeCode q reader m Q rows W G S source target) s).1.disk a=s.disk a :=
  (CommonScanProgram.pass_raw q reader (splitPass m Q rows W G S)
    source target s hsource htarget hsep).2 a ha

theorem inverse_outside (s : Machine q)
    (hsource : source+count q (Volume (Fin m) (rows*W) Q G S) ≤ q.N^q.exponent)
    (htarget : target+count q (Volume (Fin m) (rows*W) Q G S) ≤ q.N^q.exponent)
    (hsep : source+count q (Volume (Fin m) (rows*W) Q G S) ≤ target ∨
      target+count q (Volume (Fin m) (rows*W) Q G S) ≤ source)
    (a : Fin (q.N^q.exponent))
    (ha : a.val<target ∨ target+count q (Volume (Fin m) (rows*W) Q G S)≤a.val) :
    (executeRaw q (inverseCode q reader m Q rows W G S source target) s).1.disk a=s.disk a :=
  (CommonScanProgram.pass_raw q reader (gatherPass m Q rows W G S)
    source target s hsource htarget hsep).2 a ha
end Transpose

/-- Independent session slabs may occupy any distinct public disk slots.
Only their selected bases and live blocks occur in this interface. -/
structure Slabs (q : Configuration) (W n : ℕ) where
  base : Fin W → ℕ
  address : ℕ → Fin (q.N^q.exponent)
  map_at : ∀ c : Fin W, ∀ k < blockCount q.block n,
    address (c.val*blockCount q.block n+k)=CommonColumnSplit.address q (base c) k
  injective : ∀ p < W*blockCount q.block n, ∀ j < W*blockCount q.block n,
    address p=address j → p=j

/-- Standard slot allocation. Selecting only session slots permits an arbitrary
number of additional temporary or internal-edge slots in the same workspace. -/
def slotMap (q : Configuration) {W K : ℕ} (workspace stride live : ℕ)
    (slot : Fin W → Fin K) (k : ℕ) : Fin (q.N^q.exponent) :=
  if h : k/live < W then
    CommonColumnSplit.address q (workspace+(slot ⟨k/live,h⟩).val*stride) (k%live)
  else CommonColumnSplit.address q 0 0

theorem slotMap_at (q : Configuration) {W K : ℕ} (workspace stride live : ℕ)
    (slot : Fin W → Fin K) (c : Fin W) (k : ℕ) (hk : k<live) :
    slotMap q workspace stride live slot (c.val*live+k)=
      CommonColumnSplit.address q (workspace+(slot c).val*stride) k := by
  have hl : 0<live := by omega
  have hd : (c.val*live+k)/live=c.val := by
    rw [Nat.mul_comm c.val live,Nat.mul_add_div hl,Nat.div_eq_of_lt hk,Nat.add_zero]
  have hm : (c.val*live+k)%live=k := Nat.mul_add_mod_of_lt hk
  simp only [slotMap,hd,c.isLt,dif_pos,hm]

theorem slotMap_live (q : Configuration) {W K : ℕ} (workspace stride live : ℕ)
    (slot : Fin W → Fin K) (hle : live≤stride)
    (hfit : workspace+K*stride≤q.N^q.exponent)
    (k : ℕ) (hk : k<W*live) :
    workspace≤(slotMap q workspace stride live slot k).val ∧
      (slotMap q workspace stride live slot k).val<workspace+K*stride := by
  have hl : 0<live := by
    by_contra h
    have hz : live=0 := by omega
    simp [hz] at hk
  have hd : k/live<W := (Nat.div_lt_iff_lt_mul hl).2 hk
  have hm := Nat.mod_lt k hl
  have hs := (slot ⟨k/live,hd⟩).isLt
  have hmul := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hs)
  have ha : workspace+(slot ⟨k/live,hd⟩).val*stride+k%live<q.N^q.exponent := by nlinarith
  simp only [slotMap,hd,dif_pos]
  rw [CommonColumnSplit.address_val q _ _ ha]
  constructor
  · omega
  · nlinarith

theorem slotMap_injective (q : Configuration) {W K : ℕ} (workspace stride live : ℕ)
    (slot : Fin W → Fin K) (hinj : Function.Injective slot) (hle : live≤stride)
    (hfit : workspace+K*stride≤q.N^q.exponent) :
    ∀ p<W*live, ∀ k<W*live,
      slotMap q workspace stride live slot p=slotMap q workspace stride live slot k → p=k := by
  classical
  intro p hp k hk he
  have hl : 0<live := by
    by_contra h
    have hz : live=0 := by omega
    simp [hz] at hk
  have hstride : 0<stride := lt_of_lt_of_le hl hle
  have hpd : p/live<W := (Nat.div_lt_iff_lt_mul hl).2 hp
  have hkd : k/live<W := (Nat.div_lt_iff_lt_mul hl).2 hk
  have hpm := Nat.mod_lt p hl
  have hkm := Nat.mod_lt k hl
  have hpa : workspace+(slot ⟨p/live,hpd⟩).val*stride+p%live<q.N^q.exponent := by
    have hs := (slot ⟨p/live,hpd⟩).isLt
    have hm := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hs)
    nlinarith
  have hka : workspace+(slot ⟨k/live,hkd⟩).val*stride+k%live<q.N^q.exponent := by
    have hs := (slot ⟨k/live,hkd⟩).isLt
    have hm := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hs)
    nlinarith
  have hv := congrArg Fin.val he
  simp only [slotMap,hpd,hkd,dif_pos] at hv
  rw [CommonColumnSplit.address_val q _ _ hpa,CommonColumnSplit.address_val q _ _ hka] at hv
  have hslot : slot ⟨p/live,hpd⟩=slot ⟨k/live,hkd⟩ := by
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with h|h
    · have hm := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at hm
      omega
    · have hm := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at hm
      omega
  have hd : p/live=k/live := congrArg Fin.val (hinj hslot)
  have hr : p%live=k%live := by rw [hslot] at hv; omega
  have hpp := Nat.div_add_mod p live
  have hkk := Nat.div_add_mod k live
  rw [hd,hr] at hpp
  omega

def allocatedSlabs (q : Configuration) {W K : ℕ} (n workspace stride : ℕ)
    (slot : Fin W → Fin K) (hinj : Function.Injective slot)
    (hle : blockCount q.block n≤stride) (hfit : workspace+K*stride≤q.N^q.exponent) :
    Slabs q W n where
  base c := workspace+(slot c).val*stride
  address := slotMap q workspace stride (blockCount q.block n) slot
  map_at := slotMap_at q workspace stride (blockCount q.block n) slot
  injective := slotMap_injective q workspace stride (blockCount q.block n) slot hinj hle hfit

/-- The number of local bits is exactly the number of words times machine width. -/
theorem volume_word (q : Configuration) (m Q rows G S : ℕ) :
    Volume (Fin m) rows Q G (S*q.w) = Volume (Fin m) rows Q G S*q.w := by
  unfold Volume
  ring

theorem local_count (q : Configuration) (m Q rows G S : ℕ) :
    count q (Volume (Fin m) rows Q G (S*q.w))=
      blockCount q.block (Volume (Fin m) rows Q G S) := by
  rw [volume_word]
  exact CommonWordRoles.blockCount_words q.block q.w _
    (CommonLeafProgram.block_positive q) (by have := q.word_width; omega)

theorem parent_count (q : Configuration) (m Q rows W G S : ℕ) :
    count q (Volume (Fin m) (rows*W) Q G (S*q.w))=
      blockCount q.block (W*Volume (Fin m) rows Q G S) := by
  rw [local_count,←streamVolume]

section ScatterGather
variable (q : Configuration) (reader : Fin q.inventory.readers)
variable (m Q rows W G S source temporary : ℕ)
variable (slabs : Slabs q W (Volume (Fin m) rows Q G S))

/-- The two chronological machine scans which distribute the parent into selected session slots. -/
def scatterCode : List (Instruction q) :=
  transposeCode q reader m Q rows W G (S*q.w) source temporary ++
    CommonStaticSlabSplit.code q reader W (Volume (Fin m) rows Q G S) temporary slabs.address

/-- The actual slab join followed by inverse role transpose. -/
def gatherCode : List (Instruction q) :=
  CommonStaticSlabJoinMapped.code q reader (Volume (Fin m) rows Q G S) W temporary slabs.address ++
    inverseCode q reader m Q rows W G (S*q.w) temporary source

def distributionCharge : ℕ :=
  3*(2*W+6)*count q (Volume (Fin m) (rows*W) Q G (S*q.w))+
    6*(W*count q (Volume (Fin m) rows Q G (S*q.w)))

theorem scatter_safe : ∀ i ∈ scatterCode q reader m Q rows W G S source temporary slabs,
    RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact transpose_safe q reader m Q rows W G (S*q.w) source temporary i hi
  · exact CommonStaticSlabSplit.code_safe q reader W _ temporary slabs.address i hi

theorem gather_safe : ∀ i ∈ gatherCode q reader m Q rows W G S source temporary slabs,
    RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact CommonStaticSlabJoinMapped.code_safe q reader _ W temporary slabs.address i hi
  · exact inverse_safe q reader m Q rows W G (S*q.w) temporary source i hi

theorem scatter_cost : cost q (scatterCode q reader m Q rows W G S source temporary slabs)≤
    distributionCharge q m Q rows W G S := by
  rw [scatterCode,cost_append,CommonStaticSlabSplit.code_cost]
  have h := transpose_cost q reader m Q rows W G (S*q.w) source temporary
  simpa only [distributionCharge,local_count] using Nat.add_le_add_right h
    (6*(W*blockCount q.block (Volume (Fin m) rows Q G S)))

theorem scatter_length : (scatterCode q reader m Q rows W G S source temporary slabs).length≤
    distributionCharge q m Q rows W G S := by
  rw [scatterCode,List.length_append,CommonStaticSlabSplit.code_length]
  have h := transpose_length q reader m Q rows W G (S*q.w) source temporary
  simpa only [distributionCharge,local_count] using Nat.add_le_add_right h
    (6*(W*blockCount q.block (Volume (Fin m) rows Q G S)))

theorem gather_cost : cost q (gatherCode q reader m Q rows W G S source temporary slabs)≤
    distributionCharge q m Q rows W G S := by
  rw [gatherCode,cost_append,CommonStaticSlabJoinMapped.code_cost]
  have h := inverse_cost q reader m Q rows W G (S*q.w) temporary source
  simpa only [distributionCharge,local_count,Nat.add_comm] using Nat.add_le_add_left h
    (6*(W*blockCount q.block (Volume (Fin m) rows Q G S)))

theorem gather_length : (gatherCode q reader m Q rows W G S source temporary slabs).length≤
    distributionCharge q m Q rows W G S := by
  rw [gatherCode,List.length_append,CommonStaticSlabJoinMapped.code_length]
  have h := inverse_length q reader m Q rows W G (S*q.w) temporary source
  simpa only [distributionCharge,local_count,Nat.add_comm] using Nat.add_le_add_left h
    (6*(W*blockCount q.block (Volume (Fin m) rows Q G S)))

theorem scatter_raw (s : Machine q)
    (hs : source+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤q.N^q.exponent)
    (ht : temporary+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤q.N^q.exponent)
    (hsep : source+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤temporary)
    (hslab : ∀ b<blockCount q.block (W*Volume (Fin m) rows Q G S),
      ∀ p<W*blockCount q.block (Volume (Fin m) rows Q G S),
        CommonColumnSplit.address q temporary b≠slabs.address p)
    (c : Fin W) (a : Addr (Fin m) rows Q G (S*q.w)) :
    readBit q (executeRaw q (scatterCode q reader m Q rows W G S source temporary slabs) s).1.disk
      (slabs.base c) (longLayout a).val =
      readBit q s.disk source (longLayout (parentAddress c a)).val := by
  rw [scatterCode,raw_append]
  let i : Fin (Volume (Fin m) rows Q G S*q.w) :=
    finCongr (volume_word q m Q rows G S) (longLayout a)
  have h := CommonSlabReadBits.split_column_bits q reader slabs.address slabs.base
    (executeRaw q (transposeCode q reader m Q rows W G (S*q.w) source temporary) s).1
    slabs.injective hslab slabs.map_at c i
  simp only [i,finCongr_apply_coe,←volume_word q m Q rows G S] at h
  rw [h]
  exact transpose_raw q reader m Q rows W G (S*q.w) source temporary s hs ht (Or.inl hsep) c a

theorem gather_raw (s : Machine q)
    (hs : source+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤q.N^q.exponent)
    (ht : temporary+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤q.N^q.exponent)
    (hsep : source+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤temporary)
    (hslab : ∀ p<W*blockCount q.block (Volume (Fin m) rows Q G S),
      (slabs.address p).val<temporary ∨
        temporary+blockCount q.block (W*Volume (Fin m) rows Q G S)≤(slabs.address p).val)
    (c : Fin W) (a : Addr (Fin m) rows Q G (S*q.w)) :
    readBit q (executeRaw q (gatherCode q reader m Q rows W G S source temporary slabs) s).1.disk
      source (longLayout (parentAddress c a)).val =
      readBit q s.disk (slabs.base c) (longLayout a).val := by
  rw [gatherCode,raw_append,inverse_raw q reader m Q rows W G (S*q.w) temporary source _ ht hs
    (Or.inr hsep) c a]
  let i : Fin (Volume (Fin m) rows Q G S*q.w) :=
    finCongr (volume_word q m Q rows G S) (longLayout a)
  have h := CommonSlabReadBits.join_column_bits q reader slabs.address slabs.base s
    (by simpa only [parent_count] using ht) hslab slabs.map_at c i
  simpa only [i,finCongr_apply_coe,←volume_word q m Q rows G S] using h

/-- Distribution writes only the parent temporary and the selected live slab blocks. -/
theorem scatter_outside (s : Machine q)
    (hs : source+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤q.N^q.exponent)
    (ht : temporary+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤q.N^q.exponent)
    (hsep : source+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤temporary)
    (a : Fin (q.N^q.exponent))
    (ha : a.val<temporary ∨ temporary+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤a.val)
    (hslabs : ∀ k<W*blockCount q.block (Volume (Fin m) rows Q G S),a≠slabs.address k) :
    (executeRaw q (scatterCode q reader m Q rows W G S source temporary slabs) s).1.disk a=s.disk a := by
  rw [scatterCode,raw_append,CommonStaticSlabSplit.raw_outside q reader W
    (Volume (Fin m) rows Q G S) temporary slabs.address _ a hslabs]
  exact transpose_outside q reader m Q rows W G (S*q.w) source temporary s hs ht (Or.inl hsep) a ha

/-- Gathering changes only the packed temporary and the parent output interval. -/
theorem gather_outside (s : Machine q)
    (hs : source+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤q.N^q.exponent)
    (ht : temporary+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤q.N^q.exponent)
    (hsep : source+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤temporary)
    (hslab : ∀ p<W*blockCount q.block (Volume (Fin m) rows Q G S),
      (slabs.address p).val<temporary ∨
        temporary+blockCount q.block (W*Volume (Fin m) rows Q G S)≤(slabs.address p).val)
    (a : Fin (q.N^q.exponent))
    (ha : a.val<temporary ∨ temporary+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤a.val)
    (hb : a.val<source ∨ source+count q (Volume (Fin m) (rows*W) Q G (S*q.w))≤a.val) :
    (executeRaw q (gatherCode q reader m Q rows W G S source temporary slabs) s).1.disk a=s.disk a := by
  rw [gatherCode,raw_append,inverse_outside q reader m Q rows W G (S*q.w)
    temporary source _ ht hs (Or.inr hsep) a hb]
  exact CommonStaticSlabJoinMapped.raw_outside q reader (Volume (Fin m) rows Q G S)
    W temporary slabs.address s (by simpa only [parent_count] using ht) hslab a
    (by simpa only [parent_count] using ha)

/-- The local slab rounding fits within the parent rounding, so both boundary
scans are bounded by a fixed coefficient times parent blocks. -/
theorem distributionCharge_le (hW : 0<W) :
    distributionCharge q m Q rows W G S≤
      (12*W+18)*count q (Volume (Fin m) (rows*W) Q G (S*q.w)) := by
  have hvol : Volume (Fin m) rows Q G (S*q.w)≤Volume (Fin m) (rows*W) Q G (S*q.w) := by
    rw [←streamVolume]
    exact Nat.le_mul_of_pos_left _ hW
  have hcount : count q (Volume (Fin m) rows Q G (S*q.w))≤
      count q (Volume (Fin m) (rows*W) Q G (S*q.w)) := by
    by_contra h
    have hh := Nat.lt_of_not_ge h
    have hl := (cursor_live_iff (width q) (Volume (Fin m) rows Q G (S*q.w)) _
      (width_pos q)).mp hh
    have hp := (cursor_live_iff (width q) (Volume (Fin m) (rows*W) Q G (S*q.w)) _
      (width_pos q)).mpr (hl.trans_le hvol)
    exact (Nat.lt_irrefl _) hp
  unfold distributionCharge
  nlinarith [Nat.mul_le_mul_left (6*W) hcount]

end ScatterGather

end
end CodedSorting.Construction.StreamSplitMachine

#print axioms CodedSorting.Construction.StreamSplitMachine.scatter_raw
#print axioms CodedSorting.Construction.StreamSplitMachine.gather_raw
end StreamSplitMachine

section StreamParentProgram
/-!
# Same-address scalar parent program

The long-bank one-level program becomes the scalar parent exchange by the
already proved packing identity. Its instructions, charge and workspace
are unchanged: this is a specification cast, not an additional disk scan.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.Construction.StreamParentProgram

open Address CommonAddressLayout CommonSortingNormalization CommonPermutationPairs
open StreamSplitLayout
noncomputable section

/-- The scalar parent call whose field comprises `m` adjacent short fields. -/
def parentCall (m f Pref G S source buffer limit : ℕ) : ExchangeInterface.Call :=
  ⟨m*f,Pref,G,S,source,buffer,limit⟩

theorem parentCall_volume (radix m f Pref G S source buffer limit : ℕ) :
    ExchangeInterface.volume radix (parentCall m f Pref G S source buffer limit)=
      Volume (Fin m) Pref (radix^f) G S :=
  packedVolume radix m f Pref G S

/-- Retain the literal verified long-bank instruction program and expose its
identical scalar-address exchange contract. -/
def parentProgram (q : Configuration) (radix m f Pref G S source buffer limit : ℕ)
    (p : CommonFinitePermutation.Program q (Volume (Fin m) Pref (radix^f) G S)
      source buffer limit
      (longLayout.symm.trans (exchangeEquiv.trans longLayout))) :
    ExchangeInterface.Program q radix (parentCall m f Pref G S source buffer limit) where
  instructions := p.instructions
  charge := p.charge
  correct := by
    intro state y
    change readBit q (CommonStaticSchedule.executeRaw q p.instructions state).1.disk source y.val=
      readBit q state.disk source (CommonChunkLayout.swap Pref (radix^(m*f)) G S y).val
    have hp := p.correct state (finCongr (packedVolume radix m f Pref G S) y)
    have haddress := congrArg
      (fun e : Equiv.Perm (Fin (Volume (Fin m) Pref (radix^f) G S)) =>
        (e (finCongr (packedVolume radix m f Pref G S) y)).val)
      (packed_permutation radix m f Pref G S)
    simp only [Equiv.trans_apply,Equiv.symm_apply_apply,finCongr_apply_coe] at haddress
    simpa only [finCongr_apply_coe] using
      hp.trans (congrArg (readBit q state.disk source) haddress.symm)
  frame := by
    intro state a hs hb
    apply p.frame state a ?_ hb
    change a.val<source ∨ source+count q (ScalarVolume radix (m*f) Pref G S)≤a.val at hs
    rw [packedVolume] at hs
    exact hs
  safe := p.safe
  cost_le := p.cost_le
  length_le := p.length_le

/-- No instruction is inserted, removed or reordered by the parent bridge. -/
theorem parentProgram_instructions (q : Configuration)
    (radix m f Pref G S source buffer limit : ℕ)
    (p : CommonFinitePermutation.Program q (Volume (Fin m) Pref (radix^f) G S)
      source buffer limit (longLayout.symm.trans (exchangeEquiv.trans longLayout))) :
    (parentProgram q radix m f Pref G S source buffer limit p).instructions=p.instructions := rfl

/-- No I/O or instruction-length charge is hidden in the same-address cast. -/
theorem parentProgram_charge (q : Configuration)
    (radix m f Pref G S source buffer limit : ℕ)
    (p : CommonFinitePermutation.Program q (Volume (Fin m) Pref (radix^f) G S)
      source buffer limit (longLayout.symm.trans (exchangeEquiv.trans longLayout))) :
    (parentProgram q radix m f Pref G S source buffer limit p).charge=p.charge := rfl

end
end CodedSorting.Construction.StreamParentProgram

#print axioms CodedSorting.Construction.StreamParentProgram.parentProgram
#print axioms CodedSorting.Construction.StreamParentProgram.parentProgram_instructions
#print axioms CodedSorting.Construction.StreamParentProgram.parentProgram_charge
end StreamParentProgram
