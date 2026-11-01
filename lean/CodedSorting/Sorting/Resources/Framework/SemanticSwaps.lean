import CodedSorting.Interchange.Framework.Binary.Normalized
import CodedSorting.Sorting.Local.Framework.Semantic

section Swaps
/-! Columnsort's transposes on the same finite machine used by the binary
exchange.  Each adjacent swap consumes the actual disk returned by its
predecessor.  Address codecs change no stored data. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonSortingSwaps
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonFinitePermutation CommonChunkLayout CommonPrunedParameters
open PhysicalSortingExchangeLayout PhysicalSortingExchange ColumnsortExchange
open Address CoordinateScans RecursiveExchange
noncomputable section
attribute [local irreducible] CommonBinaryNormalized.normalizedProgram
  CommonBinaryNormalized.space CommonBinaryMachine.program CommonBinaryMachine.space
  CommonBinaryMachine.bound ControlledNormalization.runLogical
  Parameters.W Parameters.m radix

/-- Pull back numeric bit positions through a record permutation. -/
def bitPermutation (s w : ℕ) (e : Equiv.Perm (RecordAddress s w)) :
    Equiv.Perm (Fin (s^4*w)) :=
  (recordLayout s w).symm.trans (e.symm.trans (recordLayout s w))

theorem bitPermutation_at (s w : ℕ) (e : Equiv.Perm (RecordAddress s w))
    (a : RecordAddress s w) :
    bitPermutation s w e (recordLayout s w a)=recordLayout s w (e.symm a) := by
  simp [bitPermutation]

theorem bitPermutation_trans (s w : ℕ) (e f : Equiv.Perm (RecordAddress s w)) :
    bitPermutation s w (e.trans f)=
      (bitPermutation s w f).trans (bitPermutation s w e) := by
  ext a
  simp [bitPermutation]

theorem suffix_words (s r w : ℕ) (j : Swap) :
    suffix s r j*w=suffix s (r*w) j := by
  cases j <;> simp [suffix,Nat.mul_assoc]

theorem suffix_pos (t r : ℕ) (hr : 0<r) (j : Swap) :
    0<suffix (2^t) r j := by
  cases j <;> simp [suffix] <;> positivity

theorem stage_volume (t r w : ℕ) (j : Swap) :
    CommonChunkLayout.Volume (prefixSize (2^t) j) (2^t) 1
      (suffix (2^t) r j*w)=(2^t)^4*(r*w) := by
  rw [suffix_words]
  exact PhysicalSortingExchange.volume _ _ _

theorem same_address_val (s w : ℕ) (j : Swap) (a : RecordAddress s w) :
    (lowLayout (shape s w j a)).val=(recordLayout s w a).val :=
  congrArg Fin.val (same_address s w j a)

theorem exchange_address_val (s w : ℕ) (j : Swap) (a : RecordAddress s w) :
    (lowLayout (exchange (shape s w j a))).val=
      (recordLayout s w ((move s w j).symm a)).val := by
  have h := congrArg (shape s w j) (conjugate s w j a)
  rw [Equiv.apply_symm_apply] at h
  rw [h,same_address_val]

def stageSpace (q : Configuration) (t r : ℕ) (hr : 0<r)
    (hnormal : Normalized q) (j : Swap) : ℕ :=
  CommonBinaryNormalized.space q (prefixSize (2^t) j) t 1 (suffix (2^t) r j)
    (by omega) (suffix_pos t r hr j) hnormal

def stageCost (q : Configuration) (t r : ℕ) (j : Swap) : ℕ :=
  CommonBinaryMachine.bound q (chosenBase q) (cutoff q)
    (prefixSize (2^t) j) t 1 (suffix (2^t) r j)

def stageProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (t r source buffer limit : ℕ) (hr : 0<r) (hnormal : Normalized q) (j : Swap)
    (hs : source+count q ((2^t)^4*(r*q.w))≤buffer)
    (hw : buffer+stageSpace q t r hr hnormal j≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q ((2^t)^4*(r*q.w)) source buffer limit
      (bitPermutation (2^t) (r*q.w) (move (2^t) (r*q.w) j)) := by
  let p := CommonBinaryNormalized.normalizedProgram q reader (prefixSize (2^t) j)
    t 1 (suffix (2^t) r j) source buffer limit (by omega) (suffix_pos t r hr j)
    hnormal (by simpa only [stage_volume] using hs) hw hl
  refine ⟨p.instructions,p.charge,?_,?_,p.safe,p.cost_le,p.length_le⟩
  · intro s y
    obtain ⟨a,rfl⟩ := (recordLayout (2^t) (r*q.w)).surjective y
    have h := numeric_correct_cast (prefixSize (2^t) j) (2^t) 1
      (suffix (2^t) r j*q.w) (prefixSize (2^t) j) (2^t) 1
      (suffix (2^t) (r*q.w) j) rfl rfl rfl (suffix_words _ _ _ _)
      (readBit q s.disk source) (readBit q (executeRaw q p.instructions s).1.disk source)
      (p.correct s) (lowLayout (shape (2^t) (r*q.w) j a))
    rw [same_address_val,swap_encoded,exchange_address_val] at h
    rw [bitPermutation_at]
    exact h
  · intro s a hs' hb
    apply p.frame s a ?_ hb
    simpa only [stage_volume] using hs'

attribute [local irreducible] stageProgram

theorem stage_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (t r source buffer limit : ℕ) (hr : 0<r) (hnormal : Normalized q) (j : Swap)
    (hs : source+count q ((2^t)^4*(r*q.w))≤buffer)
    (hw : buffer+stageSpace q t r hr hnormal j≤limit)
    (hl : limit≤q.N^q.exponent) :
    (stageProgram q reader t r source buffer limit hr hnormal j hs hw hl).charge≤
      stageCost q t r j := by
  unfold stageProgram
  dsimp only
  unfold CommonBinaryNormalized.normalizedProgram stageCost
  exact CommonBinaryMachine.charge_le q reader (chosenBase q) (cutoff q)
    (prefixSize (2^t) j) t 1 (suffix (2^t) r j) source buffer limit
    (chosenBase_pos q hnormal) (by omega) (suffix_pos t r hr j) (le_refl _)
    (chosenBase_fit q hnormal) (chosenBase_startup q hnormal)
    (by simpa only [stage_volume] using hs)
    (by simpa only [stageSpace,CommonBinaryNormalized.space] using hw) hl

/-- The same workspace can be reused by all three exchanges. -/
def space (q : Configuration) (t r : ℕ) (hr : 0<r) (hnormal : Normalized q) : ℕ :=
  max (stageSpace q t r hr hnormal .last)
    (max (stageSpace q t r hr hnormal .middle) (stageSpace q t r hr hnormal .first))

theorem stageSpace_le (q : Configuration) (t r : ℕ) (hr : 0<r)
    (hnormal : Normalized q) (j : Swap) : stageSpace q t r hr hnormal j≤space q t r hr hnormal := by
  cases j
  · exact Nat.le_max_left _ _
  · exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  · exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

def exchangeCost (q : Configuration) (t r : ℕ) : ℕ :=
  max (stageCost q t r .last) (max (stageCost q t r .middle) (stageCost q t r .first))

theorem stageCost_le (q : Configuration) (t r : ℕ) (j : Swap) :
    stageCost q t r j≤exchangeCost q t r := by
  cases j
  · exact Nat.le_max_left _ _
  · exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  · exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

theorem changePermutation_charge {q : Configuration} {V source buffer limit : ℕ}
    {π π' : Equiv.Perm (Fin V)} (p : Program q V source buffer limit π) (h : π=π') :
    (p.changePermutation h).charge=p.charge := by
  subst π'
  rfl

/-- Every instruction acts on the preceding actual machine state. -/
def sequenceProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (t r source buffer limit : ℕ) (hr : 0<r) (hnormal : Normalized q)
    (hs : source+count q ((2^t)^4*(r*q.w))≤buffer)
    (hw : buffer+space q t r hr hnormal≤limit) (hl : limit≤q.N^q.exponent) :
    (js : List Swap) → Program q ((2^t)^4*(r*q.w)) source buffer limit
      (bitPermutation (2^t) (r*q.w) (permute (2^t) (r*q.w) js))
  | [] => (Program.identity q _ source buffer limit).changePermutation (by ext y; simp [bitPermutation,permute])
  | j::js =>
    ((stageProgram q reader t r source buffer limit hr hnormal j hs
      ((Nat.add_le_add_left (stageSpace_le q t r hr hnormal j) buffer).trans hw) hl).append
      (sequenceProgram q reader t r source buffer limit hr hnormal hs hw hl js)).changePermutation
        (bitPermutation_trans _ _ _ _).symm

attribute [local irreducible] sequenceProgram

theorem sequence_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (t r source buffer limit : ℕ) (hr : 0<r) (hnormal : Normalized q)
    (hs : source+count q ((2^t)^4*(r*q.w))≤buffer)
    (hw : buffer+space q t r hr hnormal≤limit) (hl : limit≤q.N^q.exponent)
    (js : List Swap) :
    (sequenceProgram q reader t r source buffer limit hr hnormal hs hw hl js).charge≤
      js.length*exchangeCost q t r := by
  induction js with
  | nil => simp only [sequenceProgram,changePermutation_charge,Program.identity,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons j js ih =>
    have h := (stage_charge_le q reader t r source buffer limit hr hnormal j hs
      ((Nat.add_le_add_left (stageSpace_le q t r hr hnormal j) buffer).trans hw) hl).trans
      (stageCost_le q t r j)
    simpa only [sequenceProgram,changePermutation_charge,Program.append,List.length_cons,
      Nat.add_mul,Nat.one_mul,Nat.add_comm] using Nat.add_le_add h ih

/-- Forward transpose: last pair, middle pair, then first pair. -/
def forwardProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (t r source buffer limit : ℕ) (hr : 0<r) (hnormal : Normalized q)
    (hs : source+count q ((2^t)^4*(r*q.w))≤buffer)
    (hw : buffer+space q t r hr hnormal≤limit) (hl : limit≤q.N^q.exponent) :
    Program q ((2^t)^4*(r*q.w)) source buffer limit
      (bitPermutation (2^t) (r*q.w) (forwardRecord (2^t) (Fin (r*q.w)))) :=
  (sequenceProgram q reader t r source buffer limit hr hnormal hs hw hl forwardSwaps).changePermutation (congrArg (bitPermutation (2^t) (r*q.w)) (forward_permute _ _))

/-- Inverse transpose reverses the order of the three field exchanges. -/
def backwardProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (t r source buffer limit : ℕ) (hr : 0<r) (hnormal : Normalized q)
    (hs : source+count q ((2^t)^4*(r*q.w))≤buffer)
    (hw : buffer+space q t r hr hnormal≤limit) (hl : limit≤q.N^q.exponent) :
    Program q ((2^t)^4*(r*q.w)) source buffer limit
      (bitPermutation (2^t) (r*q.w) (forwardRecord (2^t) (Fin (r*q.w))).symm) :=
  (sequenceProgram q reader t r source buffer limit hr hnormal hs hw hl backwardSwaps).changePermutation (congrArg (bitPermutation (2^t) (r*q.w)) (backward_permute _ _))

attribute [local irreducible] forwardProgram backwardProgram

theorem forward_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (t r source buffer limit : ℕ) (hr : 0<r) (hnormal : Normalized q)
    (hs : source+count q ((2^t)^4*(r*q.w))≤buffer)
    (hw : buffer+space q t r hr hnormal≤limit) (hl : limit≤q.N^q.exponent) :
    (forwardProgram q reader t r source buffer limit hr hnormal hs hw hl).charge≤
      3*exchangeCost q t r := by
  unfold forwardProgram
  rw [changePermutation_charge]
  exact sequence_charge_le q reader t r source buffer limit hr hnormal hs hw hl forwardSwaps

theorem backward_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (t r source buffer limit : ℕ) (hr : 0<r) (hnormal : Normalized q)
    (hs : source+count q ((2^t)^4*(r*q.w))≤buffer)
    (hw : buffer+space q t r hr hnormal≤limit) (hl : limit≤q.N^q.exponent) :
    (backwardProgram q reader t r source buffer limit hr hnormal hs hw hl).charge≤
      3*exchangeCost q t r := by
  unfold backwardProgram
  rw [changePermutation_charge]
  exact sequence_charge_le q reader t r source buffer limit hr hnormal hs hw hl backwardSwaps

/-- The record offset is unchanged by the actual forward transpose. -/
theorem forward_bit_index (s w : ℕ) (i : Fin (s^4)) (b : Fin w) :
    bitPermutation s w (forwardRecord s (Fin w)) (finProdFinEquiv (i,b))=
      finProdFinEquiv ((transpose s).symm i,b) := by
  simp [bitPermutation,recordLayout,forwardRecord,transpose]

/-- The same coordinate statement for the inverse transpose. -/
theorem backward_bit_index (s w : ℕ) (i : Fin (s^4)) (b : Fin w) :
    bitPermutation s w (forwardRecord s (Fin w)).symm (finProdFinEquiv (i,b))=
      finProdFinEquiv (transpose s i,b) := by
  simp [bitPermutation,recordLayout,forwardRecord,transpose]

/-- Forward execution yields the exact second-batch input of Columnsort. -/
theorem forward_secondInput (q : Configuration) (reader : Fin q.inventory.readers)
    (t r source buffer limit : ℕ) (hr : 0<r) (hnormal : Normalized q)
    (hs : source+count q ((2^t)^4*(r*q.w))≤buffer)
    (hw : buffer+space q t r hr hnormal≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q)
    (one : Fin (2^t) → Fin ((2^t)^2*(2^t)*1) → Fin (r*q.w) → Circuit.Bit)
    (hin : ∀ a, readBit q s.disk source (recordLayout (2^t) (r*q.w) a).val=
      PhysicalLocalSortTranspose.firstValues (2^t) (r*q.w) one a) :
    ∀ a, readBit q (executeRaw q
      (forwardProgram q reader t r source buffer limit hr hnormal hs hw hl).instructions s).1.disk
        source (recordLayout (2^t) (r*q.w) a).val=
      PhysicalLocalSortTranspose.secondValues (2^t) (r*q.w) one a := by
  intro a
  rw [(forwardProgram q reader t r source buffer limit hr hnormal hs hw hl).correct,
    bitPermutation_at,hin]
  exact congrFun (PhysicalLocalSortTranspose.forward_is_secondInput _ _ one) a

/-- The inverse consumes the actual second-batch output and supplies batch three. -/
theorem backward_thirdInput {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]
    (q : Configuration) (reader : Fin q.inventory.readers)
    (t r source buffer limit : ℕ) (hr : 0<r) (hnormal : Normalized q)
    (hs : source+count q ((2^t)^4*(r*q.w))≤buffer)
    (hw : buffer+space q t r hr hnormal≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q) (encode : α → Fin (r*q.w) → Circuit.Bit)
    (two : Fin (2^t) → Fin ((2^t)*((2^t)^2*1)) → α)
    (hin : ∀ a, readBit q s.disk source (recordLayout (2^t) (r*q.w) a).val=
      PhysicalLocalSortInverse.returnedValues (2^t) (r*q.w) encode two a) :
    ∀ a, readBit q (executeRaw q
      (backwardProgram q reader t r source buffer limit hr hnormal hs hw hl).instructions s).1.disk
        source (recordLayout (2^t) (r*q.w) a).val=
      PhysicalLocalSortInverse.thirdValues (2^t) (r*q.w) encode two a := by
  intro a
  rw [(backwardProgram q reader t r source buffer limit hr hnormal hs hw hl).correct,
    bitPermutation_at,hin]
  exact congrFun (PhysicalLocalSortInverse.backward_is_thirdInput _ _ encode two) a

end
end CodedSorting.CommonSortingSwaps
end Swaps

section ExchangeRate
/-! The improved rate for the actual common-machine Columnsort swaps.
The natural charge here is the charge proved for the concrete instruction
lists, rather than the charge of the earlier file interpreter. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonSortingExchangeRate
open CommonSortingNormalization CommonPermutationPairs CommonPrunedParameters
open CommonSortingSwaps PhysicalSortingExchange RecursiveExchange
open PhysicalArbitraryBound MainSortingParameters
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m radix CommonBinaryMachine.bound

def machineConstant : ℝ := CommonBinaryCost.binaryConstant 24 27 (6*(2*radix+6))

theorem machineConstant_nonneg : 0≤machineConstant :=
  CommonBinaryCost.binaryConstant_nonneg _ _ _

def rateConstant (r : ℕ) : ℝ :=
  machineConstant*r*(1+baseLogConstant^(1-(Parameters.epsilon : ℝ)))

theorem rateConstant_nonneg (r : ℕ) : 0≤rateConstant r := by
  unfold rateConstant
  have := machineConstant_nonneg
  have := baseLogConstant_nonneg
  positivity

theorem stage_bound (q : Configuration) (t r : ℕ) (hr : 0<r)
    (hnormal : Normalized q) (j : Swap) :
    (stageCost q t r j : ℝ)≤machineConstant*
      scan (width q) ((2^t)^4*(r*q.w))*
        (1+((t : ℝ)/chosenBase q)^(1-(Parameters.epsilon : ℝ))) := by
  have hp : 0<prefixSize (2^t) j := by
    cases j <;> simp [prefixSize] <;> positivity
  have hh := CommonBinaryCost.bound_improved (chosenBase q) (cutoff q) (width q)
    (prefixSize (2^t) j) t 1 (suffix (2^t) r j*q.w) 24 27 (6*(2*radix+6))
    (width_pos q) (chosenBase_pos q hnormal) hp (by omega)
    (Nat.mul_pos (suffix_pos t r hr j) (by have := q.word_width; omega))
    (cutoff_child q hnormal)
  have hv : BinaryPadding.Volume (prefixSize (2^t) j) (2^t) 1
      (suffix (2^t) r j*q.w)=(2^t)^4*(r*q.w) := stage_volume t r q.w j
  rw [hv] at hh
  simpa only [stageCost,CommonBinaryMachine.bound,machineConstant] using hh

theorem exchange_bound (q : Configuration) (t r : ℕ) (hr : 0<r)
    (hnormal : Normalized q) :
    (exchangeCost q t r : ℝ)≤machineConstant*
      scan (width q) ((2^t)^4*(r*q.w))*
        (1+((t : ℝ)/chosenBase q)^(1-(Parameters.epsilon : ℝ))) := by
  simpa only [exchangeCost,Nat.cast_max,max_le_iff] using
    (show _∧_∧_ from ⟨stage_bound q t r hr hnormal .last,
      stage_bound q t r hr hnormal .middle,stage_bound q t r hr hnormal .first⟩)

theorem height_le_bank (q : Configuration) : q.height≤CommonExchangeLeaf.bankWords q := by
  unfold CommonExchangeLeaf.bankWords
  omega

theorem normal_of_height (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio radix 1 Parameters.W≤q.height/q.block) :
    Normalized q :=
  hnormal.trans (Nat.div_le_div_right (height_le_bank q))

theorem normal_height_of_inventory (q : Configuration)
    (hthreshold : PhysicalLeafParameters.minimumRatio radix 1 Parameters.W≤q.inventory.ratio) :
    PhysicalLeafParameters.minimumRatio radix 1 Parameters.W≤q.height/q.block := by
  apply (Nat.le_div_iff_mul_le (CommonLeafProgram.block_positive q)).2
  exact (Nat.mul_le_mul_right q.block hthreshold).trans
    (CommonSortingNormalization.normalized_ratio q)

/-- The resident exchange bank is larger than the usable Columnsort height.
Thus its automatically selected base is sufficient for the logarithm used
by the sorting theorem; no change to the actual base is made. -/
theorem factor_height (q : Configuration) (t : ℕ)
    (hnormal : PhysicalLeafParameters.minimumRatio radix 1 Parameters.W≤q.height/q.block) :
    1+((t : ℝ)/chosenBase q)^(1-(Parameters.epsilon : ℝ))≤
      (1+baseLogConstant^(1-(Parameters.epsilon : ℝ)))*
        (1+((t : ℝ)/Real.log ((q.height : ℝ)/q.block))^(1-(Parameters.epsilon : ℝ))) := by
  have hB := CommonLeafProgram.block_positive q
  have hBR : (0 : ℝ)<q.block := by exact_mod_cast hB
  have hH := (MainSortingParameters.normalized_memory 1 q.height q.block hB hnormal).1
  have hHR : (0 : ℝ)<q.height := by exact_mod_cast (show 0<q.height by omega)
  have hh := MainSortingParameters.normalized_log_one 1 q.height q.block hB hnormal
  have hbank := normal_of_height q hnormal
  have hf := SortingExchangeBound.factor_log_bound 1 (CommonExchangeLeaf.bankWords q)
    q.block t hB hbank
  change 1+((t : ℝ)/chosenBase q)^(1-(Parameters.epsilon : ℝ))≤_ at hf
  have hlog : Real.log ((q.height : ℝ)/q.block)≤
      Real.log ((CommonExchangeLeaf.bankWords q : ℝ)/q.block) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast height_le_bank q) hBR.le
  have hdiv := div_le_div_of_nonneg_left (Nat.cast_nonneg t : (0 : ℝ)≤t)
    (show 0<Real.log ((q.height : ℝ)/q.block) by linarith) hlog
  have he : 0≤1-(Parameters.epsilon : ℝ) := by
    have := Parameters.epsilon_lt_one
    exact_mod_cast le_of_lt (sub_pos.mpr this)
  have hbanklog : 0<Real.log ((CommonExchangeLeaf.bankWords q : ℝ)/q.block) := by linarith
  have hp := Real.rpow_le_rpow (by positivity : 0≤(t : ℝ)/
    Real.log ((CommonExchangeLeaf.bankWords q : ℝ)/q.block)) hdiv he
  have := baseLogConstant_nonneg
  exact hf.trans (mul_le_mul_of_nonneg_left (add_le_add_left hp 1) (by positivity))

/-- Uniform improved rate for the exact integer charge of the machine's
three adjacent exchanges, measured in whole-record sorting blocks. -/
theorem exchange_log_bound (q : Configuration) (t r : ℕ) (hr : 0<r)
    (hnormal : PhysicalLeafParameters.minimumRatio radix 1 Parameters.W≤q.height/q.block) :
    ((exchangeCost q t r*q.block : ℕ) : ℝ)≤rateConstant r*
      (1+((t : ℝ)/Real.log ((q.height : ℝ)/q.block))^(1-(Parameters.epsilon : ℝ)))*
        (((2^t)^4+q.block : ℕ) : ℝ) := by
  have hp := exchange_bound q t r hr (normal_of_height q hnormal)
  have hs := SortingExchangeBound.scan_record_words q.block q.w r ((2^t)^4)
    (CommonLeafProgram.block_positive q) (by have := q.word_width; omega) hr
  have hf := factor_height q t hnormal
  have hm := mul_le_mul hs hf
    (by positivity : 0≤1+((t : ℝ)/chosenBase q)^(1-(Parameters.epsilon : ℝ)))
    (by positivity : 0≤(r : ℝ)*(((2^t)^4 : ℕ)+q.block))
  have hm' := mul_le_mul_of_nonneg_left hm machineConstant_nonneg
  have hp' := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg q.block : (0 : ℝ)≤q.block)
  change _≤machineConstant*scan (q.block*q.w) ((2^t)^4*(r*q.w))*_ at hp
  change _≤machineConstant*scan (q.block*q.w) ((2^t)^4*(r*q.w))*_*q.block at hp'
  push_cast at hp' hm' ⊢
  unfold rateConstant
  nlinarith only [hp',hm']

theorem actual_shape_rate (q : Configuration) (r : ℕ) (hr : 0<r)
    (hnormal : PhysicalLeafParameters.minimumRatio radix 1 Parameters.W≤q.height/q.block) :
    ActualShapeSortingBound.ActualShapeRate q.block q.height (rateConstant r)
      (Real.log ((q.height : ℝ)/q.block)) (1-(Parameters.epsilon : ℝ))
      (fun t _ => exchangeCost q t r) := by
  intro n _ _
  simpa only [LocalShape.sizeChoice] using
    exchange_log_bound q (LocalShape.sizeExponent n) r hr hnormal

end
end CodedSorting.CommonSortingExchangeRate
end ExchangeRate

section RecordSwaps
/-! The finite-machine transposes preserve complete three-word records,
including the key, payload and tag. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonSortingRecordSwaps
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonRecordProgram CommonPrunedParameters ColumnsortExchange
noncomputable section
attribute [local irreducible] CommonSortingSwaps.forwardProgram CommonSortingSwaps.backwardProgram

/-- Pure record-level transpose, expressed on the original flat record indices. -/
def forward (s : ℕ) {α : Type*} (f : Fin (s^4)→α) : Fin (s^4)→α :=
  fun i=>f ((transpose s).symm i)

def backward (s : ℕ) {α : Type*} (f : Fin (s^4)→α) : Fin (s^4)→α :=
  fun i=>f (transpose s i)

def forwardProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (t source buffer limit : ℕ) (hnormal : Normalized q)
    (hs : source+recordBlocks q ((2^t)^4)≤buffer)
    (hw : buffer+CommonSortingSwaps.space q t 3 (by omega) hnormal≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q ((2^t)^4) source buffer limit (forward (2^t)) := by
  let p := CommonSortingSwaps.forwardProgram q reader t 3 source buffer limit
    (by omega) hnormal hs hw hl
  refine ⟨p.instructions,p.charge,?_,p.frame,p.safe,p.cost_le,p.length_le⟩
  intro s f hf y
  obtain ⟨⟨i,b⟩,rfl⟩ := finProdFinEquiv.surjective y
  rw [p.correct,CommonSortingSwaps.forward_bit_index,hf,bits_at,bits_at]
  rfl

def backwardProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (t source buffer limit : ℕ) (hnormal : Normalized q)
    (hs : source+recordBlocks q ((2^t)^4)≤buffer)
    (hw : buffer+CommonSortingSwaps.space q t 3 (by omega) hnormal≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q ((2^t)^4) source buffer limit (backward (2^t)) := by
  let p := CommonSortingSwaps.backwardProgram q reader t 3 source buffer limit
    (by omega) hnormal hs hw hl
  refine ⟨p.instructions,p.charge,?_,p.frame,p.safe,p.cost_le,p.length_le⟩
  intro s f hf y
  obtain ⟨⟨i,b⟩,rfl⟩ := finProdFinEquiv.surjective y
  rw [p.correct,CommonSortingSwaps.backward_bit_index,hf,bits_at,bits_at]
  rfl

attribute [local irreducible] forwardProgram backwardProgram

theorem forward_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (t source buffer limit : ℕ) (hnormal : Normalized q)
    (hs : source+recordBlocks q ((2^t)^4)≤buffer)
    (hw : buffer+CommonSortingSwaps.space q t 3 (by omega) hnormal≤limit)
    (hl : limit≤q.N^q.exponent) :
    (forwardProgram q reader t source buffer limit hnormal hs hw hl).charge≤
      3*CommonSortingSwaps.exchangeCost q t 3 := by
  unfold forwardProgram
  exact CommonSortingSwaps.forward_charge_le q reader t 3 source buffer limit (by omega) hnormal hs hw hl

theorem backward_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (t source buffer limit : ℕ) (hnormal : Normalized q)
    (hs : source+recordBlocks q ((2^t)^4)≤buffer)
    (hw : buffer+CommonSortingSwaps.space q t 3 (by omega) hnormal≤limit)
    (hl : limit≤q.N^q.exponent) :
    (backwardProgram q reader t source buffer limit hnormal hs hw hl).charge≤
      3*CommonSortingSwaps.exchangeCost q t 3 := by
  unfold backwardProgram
  exact CommonSortingSwaps.backward_charge_le q reader t 3 source buffer limit (by omega) hnormal hs hw hl

end
end CodedSorting.CommonSortingRecordSwaps
end RecordSwaps

section SemanticSwaps
/-! The actual three-exchange programs implement the two transpose stages
of the common local sorting pipeline.  The only conversions below identify
equal numeric file lengths; all stored records remain on the same disk. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonSortingSemanticSwaps
open CommonSortingNormalization CommonRecordProgram CommonPrunedParameters
open CommonRecordReindex PhysicalLocalSortNode
noncomputable section
attribute [local irreducible] CommonSortingRecordSwaps.forwardProgram
  CommonSortingRecordSwaps.backwardProgram

theorem firstVolume (s : ℕ) : s^4=s*rows s := by unfold rows; ring

theorem secondVolume (s : ℕ) : s^4=s*(s*(s^2*1)) := by ring

theorem rowsVolume (s : ℕ) : s*rows s=s*(s*(s^2*1)) :=
  (firstVolume s).symm.trans (secondVolume s)

def forwardAtRows (q : Configuration) (s : ℕ) (f : Records q (s*rows s)) :
    Records q (s*rows s) :=
  castRecords (rowsVolume s).symm (CommonLocalSemantic.forward s f)

def backwardAtRows (q : Configuration) (s : ℕ) (f : Records q (s*rows s)) :
    Records q (s*rows s) :=
  CommonLocalSemantic.backward s (castRecords (rowsVolume s) f)

theorem forward_cast (q : Configuration) (s : ℕ) :
    castFunction q (firstVolume s) (CommonSortingRecordSwaps.forward s)=forwardAtRows q s := by
  funext f y
  obtain ⟨i,rfl⟩ := (finCongr (firstVolume s)).surjective y
  have h := CommonLocalSemantic.forward_index s f i
  simpa only [castFunction,castRecords,forwardAtRows,CommonSortingRecordSwaps.forward,
    Equiv.symm_apply_apply,finCongr_apply,finCongr_symm,Fin.cast_trans] using h.symm

theorem backward_cast (q : Configuration) (s : ℕ) :
    castFunction q (firstVolume s) (CommonSortingRecordSwaps.backward s)=backwardAtRows q s := by
  funext f y
  obtain ⟨i,rfl⟩ := (finCongr (firstVolume s)).surjective y
  have h := CommonLocalSemantic.backward_index s (castRecords (rowsVolume s) f) i
  simpa only [castFunction,castRecords,backwardAtRows,CommonSortingRecordSwaps.backward,
    Equiv.symm_apply_apply,finCongr_apply,finCongr_symm,Fin.cast_trans] using h.symm

def forwardProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (t source buffer limit : ℕ) (hnormal : Normalized q)
    (hs : source+recordBlocks q ((2^t)*rows (2^t))≤buffer)
    (hw : buffer+CommonSortingSwaps.space q t 3 (by omega) hnormal≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q ((2^t)*rows (2^t)) source buffer limit (forwardAtRows q (2^t)) :=
  (castProgram (CommonSortingRecordSwaps.forwardProgram q reader t source buffer limit
    hnormal (by simpa only [firstVolume] using hs) hw hl) (firstVolume (2^t))).changeFunction
      (forward_cast q (2^t))

def backwardProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (t source buffer limit : ℕ) (hnormal : Normalized q)
    (hs : source+recordBlocks q ((2^t)*rows (2^t))≤buffer)
    (hw : buffer+CommonSortingSwaps.space q t 3 (by omega) hnormal≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q ((2^t)*rows (2^t)) source buffer limit (backwardAtRows q (2^t)) :=
  (castProgram (CommonSortingRecordSwaps.backwardProgram q reader t source buffer limit
    hnormal (by simpa only [firstVolume] using hs) hw hl) (firstVolume (2^t))).changeFunction
      (backward_cast q (2^t))

attribute [local irreducible] forwardProgram backwardProgram

theorem forward_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (t source buffer limit : ℕ) (hnormal : Normalized q)
    (hs : source+recordBlocks q ((2^t)*rows (2^t))≤buffer)
    (hw : buffer+CommonSortingSwaps.space q t 3 (by omega) hnormal≤limit)
    (hl : limit≤q.N^q.exponent) :
    (forwardProgram q reader t source buffer limit hnormal hs hw hl).charge≤
      3*CommonSortingSwaps.exchangeCost q t 3 := by
  unfold forwardProgram
  rw [changeFunction_charge,castProgram_charge]
  exact CommonSortingRecordSwaps.forward_charge_le q reader t source buffer limit hnormal _ hw hl

theorem backward_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (t source buffer limit : ℕ) (hnormal : Normalized q)
    (hs : source+recordBlocks q ((2^t)*rows (2^t))≤buffer)
    (hw : buffer+CommonSortingSwaps.space q t 3 (by omega) hnormal≤limit)
    (hl : limit≤q.N^q.exponent) :
    (backwardProgram q reader t source buffer limit hnormal hs hw hl).charge≤
      3*CommonSortingSwaps.exchangeCost q t 3 := by
  unfold backwardProgram
  rw [changeFunction_charge,castProgram_charge]
  exact CommonSortingRecordSwaps.backward_charge_le q reader t source buffer limit hnormal _ hw hl

/-- Reindexing equal column lengths commutes with every child operation. -/
theorem batch_cast {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]
    (op : CommonLocalSemantic.Operation α) (c r r' : ℕ) (h : r=r')
    (f : Fin (c*r)→α) :
    castRecords (congrArg (fun r=>c*r) h) (CommonLocalSemantic.batch op c r f)=
      CommonLocalSemantic.batch op c r' (castRecords (congrArg (fun r=>c*r) h) f) := by
  subst r'
  rfl

/-- The second batch can use the same numeric column-length type as the first. -/
theorem batch_rows (q : Configuration) (op : CommonLocalSemantic.Operation (KeyRecordWords.Record q.w))
    (s : ℕ) (f : Records q (s*rows s)) :
    castRecords (rowsVolume s) (CommonLocalSemantic.batch op s (rows s) f)=
      CommonLocalSemantic.batch op s (s*(s^2*1)) (castRecords (rowsVolume s) f) := by
  have h : rows s=s*(s^2*1) := by unfold rows; ring
  exact batch_cast op s (rows s) (s*(s^2*1)) h f

/-- The two actual transpose adapters and their intervening child batch are
exactly the corresponding three stages of the local sorting pipeline. -/
theorem middle_stages (q : Configuration)
    (op : CommonLocalSemantic.Operation (KeyRecordWords.Record q.w))
    (s : ℕ) (f : Records q (s*rows s)) :
    backwardAtRows q s
      (CommonLocalSemantic.batch op s (rows s) (forwardAtRows q s f))=
    CommonLocalSemantic.backward s
      (CommonLocalSemantic.batch op s (s*(s^2*1)) (CommonLocalSemantic.forward s f)) := by
  unfold backwardAtRows
  rw [batch_rows]
  unfold forwardAtRows
  rw [castRecords_cancel]

end
end CodedSorting.CommonSortingSemanticSwaps
end SemanticSwaps
