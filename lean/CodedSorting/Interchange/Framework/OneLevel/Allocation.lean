import CodedSorting.Interchange.Framework.Resident.NetworkRun
import CodedSorting.Shared.Records.WordRoles.Transpose
import CodedSorting.Shared.Memory.WordAlignment

/-! Public column maps into the already allocated resident-child network.
Logical slab widths count only live words; physical slots may include the
extra padding required by three-word resident frames. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonOneLevelAllocation
open WordControl CommonSortingNormalization PhysicalStreamCursor
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge Circuit CircuitProgram ProgramNetwork
open CommonResidentNetwork
noncomputable section

abbrev address := CommonColumnSplit.address

theorem local_count (q : Configuration) (f R G S : ℕ) :
    CommonPermutationPairs.count q (longVolume f R G (S*q.w))=
      blockCount q.block (longVolume f R G S) := by
  rw [←CommonWordAlignment.volume_word]
  exact CommonWordRoles.blockCount_words q.block q.w _ (CommonLeafProgram.block_positive q)
    (by have:=q.word_width; omega)

theorem parent_volume (f R G S : ℕ) :
    longVolume f (R*Parameters.W) G S=Parameters.W*longVolume f R G S := by
  unfold longVolume
  ring

theorem parent_count (q : Configuration) (f R G S : ℕ) :
    CommonPermutationPairs.count q (longVolume f (R*Parameters.W) G (S*q.w))=
      blockCount q.block (Parameters.W*longVolume f R G S) := by
  rw [local_count,parent_volume]

theorem live_le_stride (q : Configuration) (f R G S : ℕ)
    (hV : longVolume f R G (S*q.w)≤CommonExchangeLeaf.bankBits q) :
    blockCount q.block (longVolume f R G S)≤CommonEdgeExecution.blocks q f R G (S*q.w) hV := by
  rw [←local_count]
  exact CommonEdgeExecution.count_le_blocks q f R G (S*q.w) hV

def slabMap (q : Configuration) (workspace stride liveK : ℕ)
    (files : Fin Parameters.W→File) (k : ℕ) : Fin (q.N^q.exponent) :=
  if h : k/liveK<Parameters.W then
    address q (base workspace stride (files ⟨k/liveK,h⟩)) (k%liveK)
  else address q 0 0

def inputFiles (c : Fin Parameters.W) : File := .inl (roleEnumeration.symm c)
def sinkFiles (c : Fin Parameters.W) : File :=
  .inr (.inl (sinkWire (globalProgram Parameters.d) (globalSwap (roleEnumeration.symm c))))

def inputMap (q : Configuration) (workspace stride liveK : ℕ) :=
  slabMap q workspace stride liveK inputFiles

def sinkMap (q : Configuration) (workspace stride liveK : ℕ) :=
  slabMap q workspace stride liveK sinkFiles

theorem slabMap_at (q : Configuration) (workspace stride liveK : ℕ)
    (files : Fin Parameters.W→File) (c : Fin Parameters.W) (j : ℕ) (hj : j<liveK) :
    slabMap q workspace stride liveK files (c.val*liveK+j)=
      address q (base workspace stride (files c)) j := by
  have hK : 0<liveK := by omega
  have hd : (c.val*liveK+j)/liveK=c.val := by
    rw [Nat.mul_comm c.val liveK,Nat.mul_add_div hK,Nat.div_eq_of_lt hj,Nat.add_zero]
  have hm : (c.val*liveK+j)%liveK=j := Nat.mul_add_mod_of_lt hj
  simp only [slabMap,hd,c.isLt,dif_pos,hm]

theorem inputMap_at (q : Configuration) (workspace stride liveK : ℕ)
    (c : Fin Parameters.W) (j : ℕ) (hj : j<liveK) :
    inputMap q workspace stride liveK (c.val*liveK+j)=
      address q (inputBase workspace stride (roleEnumeration.symm c)) j :=
  slabMap_at q workspace stride liveK inputFiles c j hj

theorem sinkMap_at (q : Configuration) (workspace stride liveK : ℕ)
    (c : Fin Parameters.W) (j : ℕ) (hj : j<liveK) :
    sinkMap q workspace stride liveK (c.val*liveK+j)=
      address q (edgeBase workspace stride
        (sinkWire (globalProgram Parameters.d) (globalSwap (roleEnumeration.symm c)))) j :=
  slabMap_at q workspace stride liveK sinkFiles c j hj

theorem slabMap_live (q : Configuration) (workspace stride liveK : ℕ)
    (files : Fin Parameters.W→File)
    (hle : liveK≤stride) (hfit : workspace+fileCount*stride≤q.N^q.exponent)
    (k : ℕ) (hk : k<Parameters.W*liveK) :
    workspace≤(slabMap q workspace stride liveK files k).val ∧
      (slabMap q workspace stride liveK files k).val<workspace+fileCount*stride := by
  have hK : 0<liveK := by
    by_contra h
    have hz : liveK=0 := by omega
    simp [hz] at hk
  have hd : k/liveK<Parameters.W := (Nat.div_lt_iff_lt_mul hK).2 hk
  have hm := Nat.mod_lt k hK
  have hs := slot_lt (files ⟨k/liveK,hd⟩)
  have hmul := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hs)
  have ha : base workspace stride (files ⟨k/liveK,hd⟩)+k%liveK<q.N^q.exponent := by
    dsimp only [base]; nlinarith
  simp only [slabMap,hd,dif_pos]
  rw [CommonColumnSplit.address_val q _ _ ha]
  dsimp only [base]
  constructor
  · omega
  · nlinarith

theorem slabMap_injective (q : Configuration) (workspace stride liveK : ℕ)
    (files : Fin Parameters.W→File) (hinj : Function.Injective files)
    (hle : liveK≤stride) (hfit : workspace+fileCount*stride≤q.N^q.exponent) :
    ∀ p<Parameters.W*liveK,∀ k<Parameters.W*liveK,
      slabMap q workspace stride liveK files p=slabMap q workspace stride liveK files k → p=k := by
  classical
  intro p hp k hk he
  have hK : 0<liveK := by
    by_contra h
    have hz : liveK=0 := by omega
    simp [hz] at hk
  have hpd : p/liveK<Parameters.W := (Nat.div_lt_iff_lt_mul hK).2 hp
  have hkd : k/liveK<Parameters.W := (Nat.div_lt_iff_lt_mul hK).2 hk
  have hpm := Nat.mod_lt p hK
  have hkm := Nat.mod_lt k hK
  let a : Fin Parameters.W := ⟨p/liveK,hpd⟩
  let b : Fin Parameters.W := ⟨k/liveK,hkd⟩
  have hfa := base_fits q workspace stride hfit (files a)
  have hfb := base_fits q workspace stride hfit (files b)
  have hpa : base workspace stride (files a)+p%liveK<q.N^q.exponent := by omega
  have hka : base workspace stride (files b)+k%liveK<q.N^q.exponent := by omega
  have hv := congrArg Fin.val he
  simp only [slabMap,hpd,hkd,dif_pos] at hv
  rw [CommonColumnSplit.address_val q _ _ hpa,CommonColumnSplit.address_val q _ _ hka] at hv
  have hab : files a=files b := by
    by_contra hab
    rcases base_separate workspace stride (files a) (files b) hab with h|h <;> omega
  have hd : p/liveK=k/liveK := congrArg Fin.val (hinj hab)
  have hr : p%liveK=k%liveK := by rw [hab] at hv; omega
  have hpp := Nat.div_add_mod p liveK
  have hkk := Nat.div_add_mod k liveK
  rw [hd,hr] at hpp
  omega

theorem inputFiles_injective : Function.Injective inputFiles := by
  intro a b h
  exact roleEnumeration.symm.injective (Sum.inl.inj h)

theorem inputMap_injective (q : Configuration) (workspace stride liveK : ℕ)
    (hle : liveK≤stride) (hfit : workspace+fileCount*stride≤q.N^q.exponent) :
    ∀ p<Parameters.W*liveK,∀ k<Parameters.W*liveK,
      inputMap q workspace stride liveK p=inputMap q workspace stride liveK k → p=k :=
  slabMap_injective q workspace stride liveK inputFiles inputFiles_injective hle hfit

/-- Packed parent buffers precede every network slot. -/
theorem slabMap_separate (q : Configuration) (workspace stride liveK : ℕ)
    (files : Fin Parameters.W→File)
    (hle : liveK≤stride) (hfit : workspace+fileCount*stride≤q.N^q.exponent)
    (source count : ℕ) (hs : source+count≤workspace)
    (b : ℕ) (hb : b<count) (k : ℕ) (hk : k<Parameters.W*liveK) :
    address q source b≠slabMap q workspace stride liveK files k := by
  have hl := (slabMap_live q workspace stride liveK files hle hfit k hk).1
  have ha : source+b<q.N^q.exponent := by omega
  intro he
  have hv:=congrArg Fin.val he
  rw [CommonColumnSplit.address_val q source b ha] at hv
  omega

theorem sinkMap_after (q : Configuration) (workspace stride liveK : ℕ)
    (hle : liveK≤stride) (hfit : workspace+fileCount*stride≤q.N^q.exponent)
    (target count : ℕ) (ht : target+count≤workspace)
    (k : ℕ) (hk : k<Parameters.W*liveK) :
    target+count≤(sinkMap q workspace stride liveK k).val :=
  ht.trans (slabMap_live q workspace stride liveK sinkFiles hle hfit k hk).1

end
end CodedSorting.CommonOneLevelAllocation
