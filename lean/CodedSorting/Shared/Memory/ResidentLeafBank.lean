import CodedSorting.Sorting.Local.Framework.ResidentLeafSort

/-! Word-level updates to the existing leaf bank. Initialization touches
only the length header. Payload enters through a transferred block; no
operation takes an external input function or disk snapshot. -/
set_option autoImplicit false
namespace CodedSorting.ResidentLeafBank
open WordControl ResidentLeafSort KeyRecordWords

variable {cap d w b : ℕ}

def raw (ram : RAM cap d w) (i : Fin (cap*3)) : Word w :=
  ram (i.natAdd d)

def getWord (ram : RAM cap d w) (j : ℕ) : Word w :=
  if h : j < cap*3 then raw ram ⟨j,h⟩ else 0

@[simp] theorem getWord_at (ram : RAM cap d w) (i : Fin (cap*3)) :
    getWord ram i.val = raw ram i := by
  simp only [getWord, i.isLt, ↓reduceDIte]

def initializeCount (hc : cap+1 ≤ (2^w)^d) (n : Fin (cap+1))
    (ram : RAM cap d w) : RAM cap d w :=
  Fin.append (finFunctionFinEquiv.symm (n.castLE hc)) (raw ram)

@[simp] theorem raw_initializeCount (hc : cap+1 ≤ (2^w)^d) (n : Fin (cap+1))
    (ram : RAM cap d w) : raw (initializeCount hc n ram)=raw ram := by
  funext i
  simp only [raw,initializeCount,Fin.append_right]

@[simp] theorem header_initializeCount (hc : cap+1 ≤ (2^w)^d) (n : Fin (cap+1))
    (ram : RAM cap d w) : header (initializeCount hc n ram)=
      finFunctionFinEquiv.symm (n.castLE hc) := by
  funext i
  simp only [header,initializeCount,Fin.append_left]

@[simp] theorem count_initializeCount (hc : cap+1 ≤ (2^w)^d) (n : Fin (cap+1))
    (ram : RAM cap d w) : count (initializeCount hc n ram)=n.val := by
  simp only [count,header_initializeCount,decodeWords,Equiv.apply_symm_apply,Fin.coe_castLE]
  exact Nat.mod_eq_of_lt n.isLt

/-- Copy at most `valid` words from the already-resident transfer block.
Both source and destination arrays have fixed sizes. -/
def putBlock (offset valid : ℕ) (block : Words b w) (ram : RAM cap d w) : RAM cap d w :=
  Fin.append (header ram) (fun i =>
    if h : offset ≤ i.val ∧ i.val<offset+min valid b then
      block ⟨i.val-offset,by have := Nat.min_le_right valid b; omega⟩
    else raw ram i)

@[simp] theorem header_putBlock (offset valid : ℕ) (block : Words b w) (ram : RAM cap d w) :
    header (putBlock offset valid block ram)=header ram := by
  funext i
  simp only [header,putBlock,Fin.append_left]

@[simp] theorem count_putBlock (offset valid : ℕ) (block : Words b w) (ram : RAM cap d w) :
    count (putBlock offset valid block ram)=count ram := by
  simp only [count,header_putBlock]

theorem raw_putBlock_inside (offset valid : ℕ) (block : Words b w) (ram : RAM cap d w)
    (i : Fin (cap*3)) (hlo : offset ≤ i.val) (hhi : i.val<offset+valid) (hv : valid ≤ b) :
    raw (putBlock offset valid block ram) i =
      block ⟨i.val-offset,by omega⟩ := by
  simp only [raw,putBlock,Fin.append_right,Nat.min_eq_left hv]
  rw [dif_pos ⟨hlo,hhi⟩]

theorem raw_putBlock_at (offset valid : ℕ) (block : Words b w) (ram : RAM cap d w)
    (j : Fin b) (hj : j.val<valid) (hv : valid ≤ b) (hc : offset+j.val<cap*3) :
    raw (putBlock offset valid block ram) ⟨offset+j.val,hc⟩=block j := by
  rw [raw_putBlock_inside offset valid block ram _
    (by change offset ≤ offset+j.val; omega)
    (by change offset+j.val < offset+valid; omega) hv]
  congr 1
  apply Fin.ext
  simp

theorem raw_putBlock_outside (offset valid : ℕ) (block : Words b w) (ram : RAM cap d w)
    (i : Fin (cap*3)) (hout : i.val<offset ∨ offset+valid ≤ i.val) :
    raw (putBlock offset valid block ram) i=raw ram i := by
  have hn : ¬(offset ≤ i.val ∧ i.val<offset+min valid b) := by
    have := Nat.min_le_left valid b
    omega
  simp only [raw,putBlock,Fin.append_right,dif_neg hn]

/-- Loading the next actual block extends the already-loaded prefix.
`contents` is specification-only and is not an argument of `putBlock`. -/
theorem putBlock_extends (offset total : ℕ) (block : Words b w)
    (ram : RAM cap d w) (contents : ℕ → Word w)
    (hprefix : ∀ i : Fin (cap*3), i.val < offset → raw ram i=contents i.val)
    (hblock : ∀ j : Fin b, offset+j.val < total → block j=contents (offset+j.val)) :
    ∀ i : Fin (cap*3), i.val < min total (offset+b) →
      raw (putBlock offset (min b (total-offset)) block ram) i=contents i.val := by
  intro i hi
  by_cases hbefore : i.val < offset
  · rw [raw_putBlock_outside offset (min b (total-offset)) block ram i (Or.inl hbefore)]
    exact hprefix i hbefore
  · have hlo : offset ≤ i.val := by omega
    have hhi : i.val < offset+min b (total-offset) := by omega
    have hv : min b (total-offset) ≤ b := Nat.min_le_left _ _
    rw [raw_putBlock_inside offset (min b (total-offset)) block ram i hlo hhi hv]
    have hj : i.val-offset < b := by omega
    have hcorrect := hblock ⟨i.val-offset,hj⟩ (by
      change offset+(i.val-offset) < total
      omega)
    simpa only [Nat.add_sub_of_le hlo] using hcorrect

/-- Form a block in the existing transfer bank; the unused final-block
suffix is zero padding. The valid length is read from resident metadata. -/
def getBlock (offset valid : ℕ) (ram : RAM cap d w) : Words b w :=
  fun i => if h : i.val<valid ∧ offset+i.val<cap*3 then raw ram ⟨offset+i.val,h.2⟩ else 0

def assemble (ram : RAM cap d w) (offset : ℕ) : Words b w :=
  getBlock offset (3*count ram-offset) ram

theorem assemble_at (ram : RAM cap d w) (offset : ℕ) (i : Fin b)
    (hv : offset+i.val < 3*count ram) :
    assemble ram offset i = getWord ram (offset+i.val) := by
  have hcap := count_le ram
  have hc : offset+i.val < cap*3 := by omega
  have hvalid : i.val < 3*count ram-offset := by omega
  simp only [assemble,getBlock]
  rw [dif_pos ⟨hvalid,hc⟩]
  simp only [getWord,dif_pos hc]

theorem assemble_padding (ram : RAM cap d w) (offset : ℕ) (i : Fin b)
    (hv : 3*count ram ≤ offset+i.val) : assemble ram offset i = 0 := by
  have hn : ¬(i.val < 3*count ram-offset ∧ offset+i.val < cap*3) := by omega
  simp only [assemble,getBlock,dif_neg hn]

theorem getBlock_at (offset valid : ℕ) (ram : RAM cap d w) (i : Fin b)
    (hv : i.val<valid) (hc : offset+i.val<cap*3) :
    getBlock offset valid ram i=raw ram ⟨offset+i.val,hc⟩ := by
  simp only [getBlock]
  rw [dif_pos ⟨hv,hc⟩]

theorem getBlock_padding (offset valid : ℕ) (ram : RAM cap d w) (i : Fin b)
    (hv : valid ≤ i.val ∨ cap*3 ≤ offset+i.val) : getBlock offset valid ram i=0 := by
  have hn : ¬(i.val<valid ∧ offset+i.val<cap*3) := by omega
  simp only [getBlock,dif_neg hn]

theorem recordAt_eq_of_words (hw : 2 ≤ w) (ram : RAM cap d w) (i : Fin cap)
    (record : Record w)
    (h : ∀ j : Fin 3, raw ram (finProdFinEquiv (i,j))=encode w hw record j) :
    recordAt ram i=record := by
  change decode (fun j => raw ram (finProdFinEquiv (i,j)))=record
  rw [funext h]
  exact decode_encode w hw record

theorem raw_cpu (hw : 2 ≤ w) (ram : RAM cap d w) (i : Fin (cap*3)) :
    raw (cpu hw ram) i=encode w hw (sortedRecord ram (finProdFinEquiv.symm i).1)
      (finProdFinEquiv.symm i).2 := by
  simp only [raw,cpu,Fin.append_right]

theorem raw_cpu_active (hw : 2 ≤ w) (ram : RAM cap d w)
    (i : Fin (count ram)) (j : Fin 3) :
    raw (cpu hw ram) (finProdFinEquiv
      (⟨i.val,i.isLt.trans_le (count_le ram)⟩,j))=
      encode w hw (Columnsort.sortColumn (active ram) i) j := by
  rw [raw_cpu]
  simp only [Equiv.symm_apply_apply,sortedRecord,i.isLt,↓reduceDIte]

/-- Raw words supplied by actual reads determine exactly which record
sequence the fixed resident CPU sorts. `records` is only a specification. -/
theorem cpu_exact_of_raw {n : ℕ} (hw : 2 ≤ w) (ram : RAM cap d w)
    (hn : count ram=n) (records : Fin n → Record w)
    (hraw : ∀ (i : Fin n) (j : Fin 3),
      raw ram (finProdFinEquiv
        (⟨i.val,by have hi:=i.isLt; have hc:=count_le ram; omega⟩,j))=
          encode w hw (records i) j) :
    ∀ (i : Fin n) (j : Fin 3),
      raw (cpu hw ram) (finProdFinEquiv
        (⟨i.val,by have hi:=i.isLt; have hc:=count_le ram; omega⟩,j))=
          encode w hw (Columnsort.sortColumn records i) j := by
  subst n
  have ha : active ram=records := by
    funext i
    exact recordAt_eq_of_words hw ram _ (records i) (hraw i)
  intro i j
  rw [raw_cpu_active hw ram i j,ha]

theorem abstract_cpu_exact_of_raw {n : ℕ} (hw : 2 ≤ w) (ram : RAM cap d w)
    (hn : count ram=n) (records : Fin n → Record w)
    (hraw : ∀ (i : Fin n) (j : Fin 3),
      raw ram (finProdFinEquiv
        (⟨i.val,by have hi:=i.isLt; have hc:=count_le ram; omega⟩,j))=
          encode w hw (records i) j) :
    ∀ i : Fin n,
      abstract (recordAt (cpu hw ram)
        ⟨i.val,by have hi:=i.isLt; have hc:=count_le ram; omega⟩)=
          Columnsort.sortColumn (abstract ∘ records) i := by
  have h := cpu_exact_of_raw hw ram hn records hraw
  intro i
  rw [recordAt_eq_of_words hw (cpu hw ram) _ (Columnsort.sortColumn records i) (h i)]
  exact congrFun (Columnsort.monotone_map_sortColumn records (@abstract w)
    (abstract_monotone w)) i

end CodedSorting.ResidentLeafBank
