import CodedSorting.Sorting.Local.Columnsort.ColumnsortExchange
import CodedSorting.Interchange.Framework.Fields.PhysicalExchange

section PhysicalSortingExchangeLayout
/-! The three scalar Columnsort swaps use one unchanged row-major bit file.
The codecs below expose adjacent record-address fields without moving data.
Every codec is proved to preserve the actual integer bit address. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalSortingExchangeLayout
open Circuit Address RecursiveExchange PhysicalRecursiveExchange
open PhysicalRecursiveAdapters BinaryPadding CoordinateScans ColumnsortExchange
noncomputable section

abbrev RecordAddress (s w : ℕ) := Fields s × Fin w

def recordLayout (s w : ℕ) : RecordAddress s w ≃ Fin (s^4*w) :=
  (Equiv.prodCongr (encode s) (Equiv.refl _)).trans finProdFinEquiv

theorem recordLayout_val (s w : ℕ) (a : RecordAddress s w) :
    (recordLayout s w a).val =
      (((a.1.1.val*s+a.1.2.1.val)*s+a.1.2.2.1.val)*s+a.1.2.2.2.val)*w+a.2.val := by
  change a.2.val+w*(encode s a.1).val = _
  rw [encode_val]
  ring

def pair (s : ℕ) : Fin s × Fin s ≃ Fin (s^2) :=
  finProdFinEquiv.trans (finCongr (by ring))

def shape34 (s w : ℕ) : RecordAddress s w ≃ Addr (s^2) s 1 w where
  toFun a := ⟨pair s (a.1.1,a.1.2.1),a.1.2.2.1,0,a.1.2.2.2,a.2⟩
  invFun a := ((((pair s).symm a.prefixCoord).1,
    ((pair s).symm a.prefixCoord).2,a.high,a.low),a.suffix)
  left_inv a := by simp
  right_inv a := by
    have hg : a.gap=0 := Subsingleton.elim _ _
    change FullAddress.mk (pair s ((pair s).symm a.prefixCoord)) a.high 0 a.low a.suffix=a
    rw [Equiv.apply_symm_apply,← hg]

def shape23 (s w : ℕ) : RecordAddress s w ≃ Addr s s 1 (s*w) where
  toFun a := ⟨a.1.1,a.1.2.1,0,a.1.2.2.1,finProdFinEquiv (a.1.2.2.2,a.2)⟩
  invFun a := ((a.prefixCoord,a.high,a.low,(finProdFinEquiv.symm a.suffix).1),
    (finProdFinEquiv.symm a.suffix).2)
  left_inv a := by simp
  right_inv a := by
    have hg : a.gap=0 := Subsingleton.elim _ _
    change FullAddress.mk a.prefixCoord a.high 0 a.low
      (finProdFinEquiv (finProdFinEquiv.symm a.suffix))=a
    rw [Equiv.apply_symm_apply,← hg]

def suffix12 (s w : ℕ) : (Fin s × Fin s) × Fin w ≃ Fin (s^2*w) :=
  (Equiv.prodCongr (pair s) (Equiv.refl _)).trans finProdFinEquiv

def shape12 (s w : ℕ) : RecordAddress s w ≃ Addr 1 s 1 (s^2*w) where
  toFun a := ⟨0,a.1.1,0,a.1.2.1,suffix12 s w ((a.1.2.2.1,a.1.2.2.2),a.2)⟩
  invFun a := ((a.high,a.low,((suffix12 s w).symm a.suffix).1.1,
    ((suffix12 s w).symm a.suffix).1.2),((suffix12 s w).symm a.suffix).2)
  left_inv a := by simp
  right_inv a := by
    have hg : a.gap=0 := Subsingleton.elim _ _
    have hp : a.prefixCoord=0 := Subsingleton.elim _ _
    change FullAddress.mk 0 a.high 0 a.low
      (suffix12 s w ((suffix12 s w).symm a.suffix))=a
    rw [Equiv.apply_symm_apply]
    congr 1
    · exact hp.symm
    · exact hg.symm

theorem volume34 (s w : ℕ) : Volume (s^2) s 1 w=s^4*w := by unfold Volume; ring
theorem volume23 (s w : ℕ) : Volume s s 1 (s*w)=s^4*w := by unfold Volume; ring
theorem volume12 (s w : ℕ) : Volume 1 s 1 (s^2*w)=s^4*w := by unfold Volume; ring

theorem address34 (s w : ℕ) (a : RecordAddress s w) :
    finCongr (volume34 s w) (lowLayout (shape34 s w a))=recordLayout s w a := by
  apply Fin.ext
  simp only [finCongr_apply_coe,shape34,Equiv.coe_fn_mk,lowLayout_val,pair,
    Equiv.trans_apply,finProdFinEquiv,Fin.val_zero,recordLayout_val]
  ring

theorem address23 (s w : ℕ) (a : RecordAddress s w) :
    finCongr (volume23 s w) (lowLayout (shape23 s w a))=recordLayout s w a := by
  apply Fin.ext
  simp only [finCongr_apply_coe,shape23,Equiv.coe_fn_mk,lowLayout_val,
    finProdFinEquiv,Fin.val_zero,recordLayout_val]
  ring

theorem address12 (s w : ℕ) (a : RecordAddress s w) :
    finCongr (volume12 s w) (lowLayout (shape12 s w a))=recordLayout s w a := by
  apply Fin.ext
  simp only [finCongr_apply_coe,shape12,Equiv.coe_fn_mk,lowLayout_val,suffix12,pair,
    Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.refl_apply,Prod.map_apply,
    finProdFinEquiv,Fin.val_zero,recordLayout_val]
  ring

def swap34Record (s w : ℕ) : RecordAddress s w ≃ RecordAddress s w :=
  Equiv.prodCongr (swap34 s) (Equiv.refl _)
def swap23Record (s w : ℕ) : RecordAddress s w ≃ RecordAddress s w :=
  Equiv.prodCongr (swap23 s) (Equiv.refl _)
def swap12Record (s w : ℕ) : RecordAddress s w ≃ RecordAddress s w :=
  Equiv.prodCongr (swap12 s) (Equiv.refl _)

theorem conjugate34 (s w : ℕ) (a : RecordAddress s w) :
    (shape34 s w).symm (exchange (shape34 s w a))=(swap34Record s w).symm a := by
  simp only [shape34,exchange,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,
    Equiv.symm_apply_apply,swap34Record,swap34,Equiv.prodCongr_symm,
    Equiv.prodCongr_apply,Equiv.refl_symm,Equiv.refl_apply,Prod.map_apply]
  rfl
theorem conjugate23 (s w : ℕ) (a : RecordAddress s w) :
    (shape23 s w).symm (exchange (shape23 s w a))=(swap23Record s w).symm a := by
  simp only [shape23,exchange,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,
    Equiv.symm_apply_apply,swap23Record,swap23,Equiv.prodCongr_symm,
    Equiv.prodCongr_apply,Equiv.refl_symm,Equiv.refl_apply,Prod.map_apply]
  rfl
theorem conjugate12 (s w : ℕ) (a : RecordAddress s w) :
    (shape12 s w).symm (exchange (shape12 s w a))=(swap12Record s w).symm a := by
  simp only [shape12,exchange,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,
    Equiv.symm_apply_apply,swap12Record,swap12,Equiv.prodCongr_symm,
    Equiv.prodCongr_apply,Equiv.refl_symm,Equiv.refl_apply,Prod.map_apply]
  rfl

end
end CodedSorting.PhysicalSortingExchangeLayout
end PhysicalSortingExchangeLayout

section PhysicalSortingExchange
/-! File-level Columnsort transposes. Each stage consumes the actual file
returned by the preceding stage. The only layout conversions in the proof
are equalities of physical cell addresses, not free data permutations. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace CodedSorting.PhysicalSortingExchange
open Circuit Address RecursiveExchange PhysicalRecursiveExchange PhysicalExchangeRecursion
open PhysicalRecursiveAdapters BinaryPadding CoordinateScans ColumnsortExchange
open PhysicalSortingExchangeLayout
noncomputable section

inductive Swap where
  | last | middle | first
  deriving DecidableEq

def prefixSize (s : ℕ) : Swap → ℕ
  | .last => s^2 | .middle => s | .first => 1
def suffix (s w : ℕ) : Swap → ℕ
  | .last => w | .middle => s*w | .first => s^2*w
def shape (s w : ℕ) : (j : Swap) → RecordAddress s w ≃ Addr (prefixSize s j) s 1 (suffix s w j)
  | .last => shape34 s w | .middle => shape23 s w | .first => shape12 s w
def move (s w : ℕ) : Swap → RecordAddress s w ≃ RecordAddress s w
  | .last => swap34Record s w | .middle => swap23Record s w | .first => swap12Record s w

theorem volume (s w : ℕ) (j : Swap) :
    Volume (prefixSize s j) s 1 (suffix s w j)=s^4*w := by
  cases j
  · exact volume34 s w
  · exact volume23 s w
  · exact volume12 s w

theorem same_address (s w : ℕ) (j : Swap) (a : RecordAddress s w) :
    finCongr (volume s w j) (lowLayout (shape s w j a))=recordLayout s w a := by
  cases j
  · exact address34 s w a
  · exact address23 s w a
  · exact address12 s w a

theorem conjugate (s w : ℕ) (j : Swap) (a : RecordAddress s w) :
    (shape s w j).symm (exchange (shape s w j a))=(move s w j).symm a := by
  cases j
  · exact conjugate34 s w a
  · exact conjugate23 s w a
  · exact conjugate12 s w a

theorem shape_input (s w B : ℕ) (hB : 0 < B) (j : Swap) (F : RecordAddress s w → Bit) :
    represented lowLayout B hB (F ∘ (shape s w j).symm)=
      represented (recordLayout s w) B hB F := by
  rw [← represented_cast lowLayout (volume s w j)]
  exact represented_regroup _ _ _ (same_address s w j) B hB F

theorem shape_output (s w B : ℕ) (hB : 0 < B) (j : Swap) (F : RecordAddress s w → Bit) :
    represented lowLayout B hB (transport exchangeEquiv (F ∘ (shape s w j).symm))=
      represented (recordLayout s w) B hB (transport (move s w j) F) := by
  rw [regroup_exchange_file _ _ _ _ (same_address s w j)]
  congr 1
  funext a
  change F ((shape s w j).symm (exchange (shape s w j a)))=F ((move s w j).symm a)
  rw [conjugate]

/-- `B` is the block width in bits; `w` is the complete record width in bits.
They are independent, so three-word key/payload/tag records use `w=3*wordBits`. -/
def stage (base cutoff B : ℕ) (hB : 0 < B) (t w : ℕ) (j : Swap)
    (source : File) : Option Result :=
  PhysicalBinaryExchange.execute base cutoff B hB (prefixSize (2^t) j) t 1 (suffix (2^t) w j) source

def stageBound (base cutoff B t w : ℕ) (j : Swap) : ℕ :=
  PhysicalBinaryExchange.bound base cutoff B (prefixSize (2^t) j) t 1 (suffix (2^t) w j)

theorem stage_correct (base cutoff B : ℕ) (hB : 0 < B) (hb : 0 < base)
    (hstartup : (radix^base*radix^base)*B ≤ cutoff+B)
    (t w : ℕ) (hw : 0 < w) (j : Swap) (F : RecordAddress (2^t) w → Bit) :
    ∃ out, stage base cutoff B hB t w j (represented (recordLayout (2^t) w) B hB F)=some out ∧
      out.1=represented (recordLayout (2^t) w) B hB (transport (move (2^t) w j) F) ∧
      out.2≤stageBound base cutoff B t w j := by
  have hs : 0 < suffix (2^t) w j := by cases j <;> simp [suffix] <;> positivity
  let E := F ∘ (shape (2^t) w j).symm
  obtain ⟨out,hr,ho,hc⟩ := PhysicalBinaryExchange.execute_correct_cost base cutoff B hB hb
    hstartup (prefixSize (2^t) j) t 1 (suffix (2^t) w j) (by omega) hs (encoded lowLayout E)
  have hin : canonical B hB (encoded lowLayout E)=represented (recordLayout (2^t) w) B hB F :=
    shape_input (2^t) w B hB j F
  have hout : canonical B hB (PhysicalPaddingExchange.exchanged (encoded lowLayout E))=
      represented (recordLayout (2^t) w) B hB (transport (move (2^t) w j) F) := by
    rw [← PhysicalPaddedChunks.represented_exchanged]
    have he : encoded lowLayout E ∘ lowLayout=E := by
      funext a
      simp only [encoded,Function.comp_apply,Equiv.symm_apply_apply]
    rw [he]
    exact shape_output (2^t) w B hB j F
  exact ⟨out,hin ▸ hr,ho.trans hout,hc⟩

/-- Execute a sequence of adjacent swaps on one evolving physical file. -/
def execute (base cutoff B : ℕ) (hB : 0 < B) (t w : ℕ) : List Swap → File → Option Result
  | [], source => some (source,0)
  | j::js, source => do
      let first ← stage base cutoff B hB t w j source
      let rest ← execute base cutoff B hB t w js first.1
      return (rest.1,first.2+rest.2)

def permute (s w : ℕ) : List Swap → Equiv.Perm (RecordAddress s w)
  | [] => Equiv.refl _
  | j::js => (move s w j).trans (permute s w js)

def charge (base cutoff B t w : ℕ) (js : List Swap) : ℕ :=
  (js.map (stageBound base cutoff B t w)).sum

theorem execute_correct (base cutoff B : ℕ) (hB : 0 < B) (hb : 0 < base)
    (hstartup : (radix^base*radix^base)*B ≤ cutoff+B)
    (t w : ℕ) (hw : 0 < w) (js : List Swap) (F : RecordAddress (2^t) w → Bit) :
    ∃ out, execute base cutoff B hB t w js (represented (recordLayout (2^t) w) B hB F)=some out ∧
      out.1=represented (recordLayout (2^t) w) B hB (transport (permute (2^t) w js) F) ∧
      out.2≤charge base cutoff B t w js := by
  induction js generalizing F with
  | nil => exact ⟨(_,0),rfl,rfl,by simp [charge]⟩
  | cons j js ih =>
    obtain ⟨one,hr1,ho1,hc1⟩ := stage_correct base cutoff B hB hb hstartup t w hw j F
    obtain ⟨rest,hrr,hor,hcr⟩ := ih (transport (move (2^t) w j) F)
    refine ⟨(rest.1,one.2+rest.2),?_,?_,?_⟩
    · simp [execute,hr1,ho1,hrr]
    · simpa only [permute,transport_comp] using hor
    · simpa only [charge,List.map_cons,List.sum_cons] using Nat.add_le_add hc1 hcr

def forwardSwaps : List Swap := [.last,.middle,.first]
def backwardSwaps : List Swap := [.first,.middle,.last]

theorem forward_permute (s w : ℕ) :
    permute s w forwardSwaps=forwardRecord s (Fin w) := by
  apply Equiv.ext
  intro a
  rfl

theorem backward_permute (s w : ℕ) :
    permute s w backwardSwaps=(forwardRecord s (Fin w)).symm := by
  apply Equiv.ext
  intro a
  rfl

end
end CodedSorting.PhysicalSortingExchange
end PhysicalSortingExchange
