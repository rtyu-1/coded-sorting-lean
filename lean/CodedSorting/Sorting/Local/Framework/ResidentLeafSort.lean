import CodedSorting.Shared.Records.KeyRecordWords
import CodedSorting.Shared.Words.WordConvention

/-! The terminal Columnsort computation on counted resident words.
The length header occupies d words and each key/payload/sentinel record
occupies three words. The CPU function depends only on this one bank;
neither a previous RAM snapshot nor an input-dependent function is retained.
This module covers the resident computation, not its disk load/store loop. -/

set_option autoImplicit false
namespace CodedSorting.ResidentLeafSort
open WordControl KeyRecordWords Columnsort

instance recordOrder (w : ℕ) : LinearOrder (Record w) :=
  LinearOrder.lift' (@abstract w) (abstract_injective w)

theorem abstract_monotone (w : ℕ) : Monotone (@abstract w) := fun _ _ h => h

def residentWords (cap d : ℕ) : ℕ := d+cap*3

abbrev RAM (cap d w : ℕ) := Words (residentWords cap d) w

def header {cap d w : ℕ} (ram : RAM cap d w) : Words d w :=
  fun i => ram (i.castAdd (cap*3))

def count {cap d w : ℕ} (ram : RAM cap d w) : ℕ :=
  decodeWords (header ram) % (cap+1)

theorem count_le {cap d w : ℕ} (ram : RAM cap d w) : count ram ≤ cap := by
  have h := Nat.mod_lt (decodeWords (header ram)) (show 0<cap+1 by omega)
  exact Nat.le_of_lt_succ h

def recordAt {cap d w : ℕ} (ram : RAM cap d w) (i : Fin cap) : Record w :=
  decode (fun j => ram ((finProdFinEquiv (i,j)).natAdd d))

def active {cap d w : ℕ} (ram : RAM cap d w) : Fin (count ram) → Record w :=
  fun i => recordAt ram ⟨i.val,i.isLt.trans_le (count_le ram)⟩

def sortedRecord {cap d w : ℕ} (ram : RAM cap d w) (i : Fin cap) : Record w :=
  if h : i.val<count ram then sortColumn (active ram) ⟨i.val,h⟩ else recordAt ram i

/-- This is a fixed CPU instruction on exactly d+3*cap resident words. -/
def cpu {cap d w : ℕ} (hw : 2≤w) (ram : RAM cap d w) : RAM cap d w :=
  Fin.append (header ram) (fun i =>
    encode w hw (sortedRecord ram (finProdFinEquiv.symm i).1)
      (finProdFinEquiv.symm i).2)

@[simp] theorem header_cpu {cap d w : ℕ} (hw : 2≤w) (ram : RAM cap d w) :
    header (cpu hw ram)=header ram := by
  funext i
  simp [header,cpu,residentWords]

@[simp] theorem count_cpu {cap d w : ℕ} (hw : 2≤w) (ram : RAM cap d w) :
    count (cpu hw ram)=count ram := by simp only [count,header_cpu]

@[simp] theorem recordAt_cpu {cap d w : ℕ} (hw : 2≤w) (ram : RAM cap d w)
    (i : Fin cap) : recordAt (cpu hw ram) i=sortedRecord ram i := by
  unfold recordAt cpu
  simp only [Fin.append_right,Equiv.symm_apply_apply]
  exact decode_encode w hw _

theorem active_sorted {cap d w : ℕ} (hw : 2≤w) (ram : RAM cap d w)
    (i : Fin (count ram)) :
    recordAt (cpu hw ram) ⟨i.val,i.isLt.trans_le (count_le ram)⟩ =
      sortColumn (active ram) i := by
  rw [recordAt_cpu]
  simp only [sortedRecord,i.isLt,↓reduceDIte,Fin.eta]

/-- The old unbounded-record leaf and the concrete word bank give exactly
the same sorted records, not just two independently sorted permutations. -/
theorem abstract_leaf_exact {cap d w : ℕ} (hw : 2≤w) (ram : RAM cap d w) :
    (fun i : Fin (count ram) => abstract
      (recordAt (cpu hw ram) ⟨i.val,i.isLt.trans_le (count_le ram)⟩)) =
      sortColumn (abstract ∘ active ram) := by
  have h := monotone_map_sortColumn (active ram) (@abstract w) (abstract_monotone w)
  funext i
  rw [active_sorted]
  exact congrFun h i

theorem active_permutation {cap d w : ℕ} (hw : 2≤w) (ram : RAM cap d w) :
    (List.ofFn (fun i : Fin (count ram) =>
      recordAt (cpu hw ram) ⟨i.val,i.isLt.trans_le (count_le ram)⟩)).Perm
        (List.ofFn (active ram)) := by
  simpa only [active_sorted] using sortColumn_perm (active ram)

/-- Valid headers need only the exact finite capacity inequality; there is
no hidden assumption that the length fits in one word. -/
def initializeBank (cap d w : ℕ) (hw : 2≤w) (hc : cap+1≤(2^w)^d)
    (n : Fin (cap+1)) (records : Fin cap → Record w) : RAM cap d w :=
  Fin.append (finFunctionFinEquiv.symm (n.castLE hc))
    (fun i => encode w hw (records (finProdFinEquiv.symm i).1)
      (finProdFinEquiv.symm i).2)

@[simp] theorem count_initializeBank (cap d w : ℕ) (hw : 2≤w)
    (hc : cap+1≤(2^w)^d) (n : Fin (cap+1)) (records : Fin cap → Record w) :
    count (initializeBank cap d w hw hc n records)=n.val := by
  have hh : header (initializeBank cap d w hw hc n records)=
      finFunctionFinEquiv.symm (n.castLE hc) := by
    funext i
    simp [header,initializeBank,residentWords]
  simp only [count,hh,decodeWords,Equiv.apply_symm_apply,Fin.coe_castLE]
  exact Nat.mod_eq_of_lt n.isLt

@[simp] theorem recordAt_initializeBank (cap d w : ℕ) (hw : 2≤w)
    (hc : cap+1≤(2^w)^d) (n : Fin (cap+1)) (records : Fin cap → Record w)
    (i : Fin cap) : recordAt (initializeBank cap d w hw hc n records) i=records i := by
  unfold recordAt initializeBank
  simp only [Fin.append_right,Equiv.symm_apply_apply]
  exact decode_encode w hw _

/-- The instruction is selected independently of the input and modifies
only the existing RAM; its disk is unchanged and its I/O charge is zero. -/
def instruction {cap d w : ℕ} (hw : 2≤w) :
    BitWordPacking.Operation (Word w) (residentWords cap d) := .cpu (cpu hw)

theorem instruction_semantics {cap d w : ℕ} (hw : 2≤w)
    (s : BitWordPacking.State (Word w) (residentWords cap d)) :
    (BitWordPacking.step (instruction hw) s).ram=cpu hw s.ram ∧
    (BitWordPacking.step (instruction hw) s).disk=s.disk ∧
    BitWordPacking.transferCost (instruction (cap:=cap) (d:=d) hw)=0 := by
  exact ⟨rfl,rfl,rfl⟩

theorem memory_fit (M cap d : ℕ) (h : d+3*cap≤M) : residentWords cap d≤M := by
  simpa only [residentWords,Nat.mul_comm] using h

end CodedSorting.ResidentLeafSort
