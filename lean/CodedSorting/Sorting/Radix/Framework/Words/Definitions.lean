import CodedSorting.Shared.Records.RecordOperations
import CodedSorting.Sorting.Radix.Model.ExternalMSD

/-! The ordinary finite-word record sorter used at every MSD local call.
Original keys and payloads are retained. Its output is literally the
`sortColumn` output established by `CommonLocalMachine`; no disk execution
or rekeying operation is asserted in this semantic module. -/
set_option autoImplicit false
namespace CodedSorting.CommonWordMSD
open WordControl KeyRecordWords Columnsort
noncomputable section

/-- Sentinels are ordered outside all ordinary word keys. -/
def key {w : ℕ} : Record w → ℕ
  | .bottom => 0
  | .data k _ => k.val
  | .top => 2^w

theorem data_key_order {w : ℕ} (k x l y : Word w)
    (h : Record.data k x ≤ Record.data l y) : k≤l := by
  have h' : toLex (k.val,x.val) ≤ toLex (l.val,y.val) := by
    change abstract (Record.data k x) ≤ abstract (Record.data l y) at h
    simpa only [abstract,WithBot.coe_le_coe,WithTop.coe_le_coe] using h
  exact Prod.Lex.monotone_fst _ _ h'

theorem key_monotone (w : ℕ) : Monotone (@key w) := by
  intro a b hab
  cases a with
  | bottom => exact Nat.zero_le _
  | data k x =>
    cases b with
    | bottom =>
      change abstract (Record.data k x)≤abstract (Record.bottom : Record w) at hab
      simp [abstract] at hab
    | data l y => exact data_key_order k x l y hab
    | top => exact Nat.le_of_lt k.isLt
  | top =>
    cases b with
    | bottom =>
      change abstract (Record.top : Record w)≤abstract (Record.bottom : Record w) at hab
      simp [abstract] at hab
    | data k x =>
      change abstract (Record.top : Record w)≤abstract (Record.data k x) at hab
      simp [abstract] at hab
    | top => exact le_rfl

def localSort {w : ℕ} (xs : List (Record w)) : List (Record w) :=
  List.ofFn (sortColumn xs.get)

theorem localSort_perm {w : ℕ} (xs : List (Record w)) : (localSort xs).Perm xs := by
  simpa [localSort] using sortColumn_perm xs.get

theorem localSort_pairwise {w : ℕ} (xs : List (Record w)) :
    (localSort xs).Pairwise (fun x y => key x≤key y) := by
  exact (sortColumn_monotone xs.get).ofFn_sorted.imp (fun h => key_monotone w h)

theorem localSort_correct {w : ℕ} (xs : List (Record w)) :
    (localSort xs).Perm xs ∧ (localSort xs).Pairwise (fun x y => key x≤key y) :=
  ⟨localSort_perm xs,localSort_pairwise xs⟩

/-- The list adapter adds no data transformation to the finite-array output. -/
theorem localSort_ofFn {w n : ℕ} (f : Fin n → Record w) :
    localSort (List.ofFn f)=List.ofFn (sortColumn f) := by
  have hp : (localSort (List.ofFn f)).Perm (List.ofFn (sortColumn f)) :=
    (localSort_perm _).trans (sortColumn_perm f).symm
  have hleft : (localSort (List.ofFn f)).Pairwise (·≤·) :=
    (sortColumn_monotone (List.ofFn f).get).ofFn_sorted
  have hright := (sortColumn_monotone f).ofFn_sorted
  exact List.eq_of_perm_of_sorted hp hleft hright

/-- A fully sorted chunk also has sorted current digits when the higher
prefix is fixed. This permits an MSD implementation to retain full keys. -/
theorem digit_mono_fixed_prefix (base remaining x y : ℕ) (hb : 0<base)
    (hxy : x≤y) (hp : x/base^(remaining+1)=y/base^(remaining+1)) :
    MSD.digit base hb remaining x≤MSD.digit base hb remaining y := by
  have hq := Nat.div_le_div_right (c:=base^remaining) hxy
  have hp' : (x/base^remaining)/base=(y/base^remaining)/base := by
    simpa only [Nat.div_div_eq_div_mul,pow_succ] using hp
  have hx := Nat.mod_add_div (x/base^remaining) base
  have hy := Nat.mod_add_div (y/base^remaining) base
  change x/base^remaining%base≤y/base^remaining%base
  rw [hp'] at hx
  omega

end
end CodedSorting.CommonWordMSD
