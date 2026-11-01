import CodedSorting.Sorting.Bounds.GlobalSortingBound

section PhysicalLocalSortInverse
/-! The actual inverse transpose supplies precisely the third batch of the
existing finite Columnsort algorithm. Both sides retain the complete record
encoding; no intermediate sorted file is reconstructed from an oracle. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalLocalSortInverse
open Circuit Address RecursiveExchange PhysicalRecursiveExchange PhysicalExchangeRecursion
open PhysicalSortingExchangeLayout PhysicalSortingExchange PhysicalLocalSortTranspose
open ColumnsortExchange RecursiveColumnsort
noncomputable section

variable {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]

theorem afterTwoTape_at (q s : ℕ) (two : Fin s → Fin (s*(q*1)) → α)
    (p : Fin (s*q)) (c : Fin s) :
    afterTwoTape q s two ((finProdFinEquiv (p,finProdFinEquiv (c,(0 : Fin 1)))) :
      Fin (s*q*(s*1))) = two c (finCongr (by ring) p) := by
  let j : Fin (s*q*(s*1)) := finProdFinEquiv (p,finProdFinEquiv (c,(0 : Fin 1)))
  have hj : (0 : ℤ) ≤ j ∧ (j : ℤ)<(s*q*(s*1) : ℕ) :=
    ⟨by exact_mod_cast Nat.zero_le j.val,by exact_mod_cast j.isLt⟩
  change afterTwoTape q s two (j : ℤ)=_
  simp only [afterTwoTape,dif_pos hj,Int.toNat_natCast,Fin.eta]
  dsimp only [j]
  simp only [Equiv.symm_apply_apply,Fin.val_zero,Nat.mul_one,Nat.add_zero]
  rfl

def prefixThree (s : ℕ) (x : Fields s) : Fin (s*s^2) :=
  finProdFinEquiv (x.1,pair s (x.2.1,x.2.2.1))

def returnedValues (s w : ℕ) (code : α → Fin w → Bit)
    (two : Fin s → Fin (s*(s^2*1)) → α) (a : RecordAddress s w) : Bit :=
  code (two a.1.1 (secondRow s a.1)) a.2

def thirdValues (s w : ℕ) (code : α → Fin w → Bit)
    (two : Fin s → Fin (s*(s^2*1)) → α) (a : RecordAddress s w) : Bit :=
  code (gridInput (s^2*s*1) 0 (afterTwoTape (s^2) s two)
    a.1.1 (firstRow s a.1)) a.2

theorem backward_is_thirdInput (s w : ℕ) (code : α → Fin w → Bit)
    (two : Fin s → Fin (s*(s^2*1)) → α) :
    transport (forwardRecord s (Fin w)).symm (returnedValues s w code two)=
      thirdValues s w code two := by
  funext a
  have h := afterTwoTape_at (s^2) s two (prefixThree s a.1) a.1.2.2.2
  have hi : (0 : ℤ)+(a.1.1 : ℤ)*((s^2*s*1 : ℕ) : ℤ)+(firstRow s a.1 : ℤ)=
      ((finProdFinEquiv (prefixThree s a.1,finProdFinEquiv (a.1.2.2.2,(0 : Fin 1)))) :
        Fin (s*s^2*(s*1))) := by
    change (0 : ℤ)+(a.1.1 : ℤ)*(s^2*s*1)+
      ((a.1.2.2.2.val+s*(a.1.2.2.1.val+s*a.1.2.1.val) : ℕ) : ℤ)=
      (((0+1*a.1.2.2.2.val)+(s*1)*((a.1.2.2.1.val+s*a.1.2.1.val)+s^2*a.1.1.val) : ℕ) : ℤ)
    push_cast
    ring
  unfold thirdValues gridInput
  rw [hi,h]
  change code (two a.1.2.2.2 (secondRow s (a.1.2.2.2,a.1.1,a.1.2.1,a.1.2.2.1))) a.2 = _
  congr 2
  apply Fin.ext
  change (a.1.2.2.1.val+s*a.1.2.1.val)+(s^2*1)*a.1.1.val=
    (a.1.2.2.1.val+s*a.1.2.1.val)+s^2*a.1.1.val
  ring

theorem six_swaps_to_third (reserve H B w r t : ℕ)
    (hreserve : 0 < reserve) (hB : 0 < B) (hw : 0 < w) (hr : 0 < r)
    (hnormal : PhysicalLeafParameters.minimumRatio radix reserve Parameters.W ≤ H/B)
    (one : Fin (2^t) → Fin ((2^t)^2*(2^t)*1) → Fin (r*w) → Bit)
    (code : α → Fin (r*w) → Bit)
    (two : Fin (2^t) → Fin ((2^t)*((2^t)^2*1)) → α)
    (batch : File → Option Result) (mid : Result)
    (hbatch : batch (represented (recordLayout (2^t) (r*w)) (B*w) (Nat.mul_pos hB hw)
      (secondValues (2^t) (r*w) one))=some mid)
    (hmid : mid.1=represented (recordLayout (2^t) (r*w)) (B*w) (Nat.mul_pos hB hw)
      (returnedValues (2^t) (r*w) code two)) :
    ∃ out,
      aroundBatch (NormalizedPhysicalExchange.chosenBase H B)
        (NormalizedPhysicalExchange.cutoff reserve H w) (B*w) (Nat.mul_pos hB hw)
        t (r*w) batch (represented (recordLayout (2^t) (r*w)) (B*w) (Nat.mul_pos hB hw)
          (firstValues (2^t) (r*w) one))=some out ∧
      out.1=represented (recordLayout (2^t) (r*w)) (B*w) (Nat.mul_pos hB hw)
        (thirdValues (2^t) (r*w) code two) ∧
      out.2≤6*SortingExchangeBound.exchangeCost reserve H B w r t ((2^t)^4)+mid.2 := by
  obtain ⟨out,he,ho,hc⟩ := PhysicalSortingExchangeCost.six_swaps_actual_cost
    reserve H B w r t hreserve hB hw hr hnormal one batch mid
    (returnedValues (2^t) (r*w) code two) hbatch hmid
  rw [backward_is_thirdInput] at ho
  exact ⟨out,he,ho,hc⟩

end
end CodedSorting.PhysicalLocalSortInverse
end PhysicalLocalSortInverse

section PhysicalLocalSortScan
/-! Actual scans for the half-column shift and its removal. Padding bits
come from public sentinel encodings. Payload bits are read once from the
current file, and one persistent writer packs across both boundaries. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalLocalSortScan
open Circuit PhysicalRecursiveExchange PhysicalExchangeRecursion
open BucketMachine BucketReader StreamCopy
noncomputable section

def paddingValues (n offset : ℕ) (value : ℕ → Bit) : List Bit :=
  (List.range' offset n).map value

def emit (B : ℕ) (value : ℕ → Bit) : ℕ → ℕ → Writer Bit → Writer Bit
  | 0, _, writer => writer
  | n+1, offset, writer => emit B value n (offset+1) (writer.push B (value offset))

theorem emit_correct (B : ℕ) (value : ℕ → Bit) (n offset : ℕ) (writer : Writer Bit)
    (hw : writer.Valid B) :
    (emit B value n offset writer).Valid B ∧
      (emit B value n offset writer).contents=writer.contents++paddingValues n offset value := by
  induction n generalizing offset writer with
  | zero => exact ⟨hw,by simp [emit,paddingValues]⟩
  | succ n ih =>
    obtain ⟨hv,hc⟩ := ih (offset+1) (writer.push B (value offset)) (Writer.push_valid B _ _ hw)
    exact ⟨hv,by simpa [emit,paddingValues,Writer.push_contents,List.append_assoc] using hc⟩

def addMargins (B N L R : ℕ) (left right : ℕ → Bit) (source : File) : Option Result := do
  let copied ← StreamCopy.run B N
    ⟨Reader.fromDisk source,emit B left L 0 Writer.empty⟩
  let writer := emit B right R 0 copied.target
  return (writer.finish,copied.source.reads+writer.finish.length)

theorem addMargins_correct (B : ℕ) (hB : 0 < B) (L R : ℕ) (left right : ℕ → Bit)
    (xs : List Bit) (source : File) (hv : (Reader.fromDisk source).Valid B)
    (hf : source.flatten=xs) :
    addMargins B xs.length L R left right source=
      some (pack B hB (paddingValues L 0 left++xs++paddingValues R 0 right),
        source.length+(L+xs.length+R+B-1)/B) := by
  have hl := emit_correct B left L 0 Writer.empty (Writer.empty_valid B hB)
  obtain ⟨copied,hcopy,hvalid,hrest,hcontents,hreads⟩ := copy_prefix B xs []
    ⟨Reader.fromDisk source,emit B left L 0 Writer.empty⟩ ⟨hv,hl.1⟩
    (by simpa [Reader.contents,Reader.fromDisk] using hf)
  have hd := Reader.empty_contents_disk B copied.source hvalid.1 hrest
  have hr : copied.source.reads=source.length := by
    simpa [Reader.fromDisk,hd] using hreads
  have he := emit_correct B right R 0 copied.target hvalid.2
  have hc : (emit B right R 0 copied.target).contents=
      paddingValues L 0 left++xs++paddingValues R 0 right := by
    rw [he.2,hcontents,hl.2]
    simp [Writer.contents,Writer.empty,List.append_assoc]
  have hout : (emit B right R 0 copied.target).finish=
      pack B hB (paddingValues L 0 left++xs++paddingValues R 0 right) := by
    rw [DiskStreamPass.writer_finish_eq_pack B hB _ he.1,hc]
  simp [addMargins,hcopy,hr,hout,pack_count,paddingValues,Nat.add_assoc]

/-- Consume a prefix while retaining the same reader buffer. -/
def skip : ℕ → Reader Bit → Option (Reader Bit)
  | 0, reader => some reader
  | n+1, reader => reader.pop.bind (fun p => skip n p.2)

theorem skip_correct (B : ℕ) (front back : List Bit) (reader : Reader Bit)
    (hv : reader.Valid B) (hf : reader.contents=front++back) :
    ∃ out, skip front.length reader=some out ∧ out.Valid B ∧ out.contents=back ∧
      out.reads+out.disk.length=reader.reads+reader.disk.length := by
  induction front generalizing reader with
  | nil => exact ⟨reader,rfl,hv,by simpa using hf,rfl⟩
  | cons x xs ih =>
    obtain ⟨next,hpop⟩ := Reader.pop_exists B reader hv x (xs++back) (by simpa using hf)
    have hn := Reader.pop_valid B _ _ _ hv hpop
    have hc : next.contents=xs++back := by
      have h := Reader.pop_contents _ _ _ hpop
      rw [hf] at h
      exact (List.cons.inj h).2.symm
    obtain ⟨out,he,hv',hc',hr⟩ := ih next hn hc
    exact ⟨out,by simp [skip,hpop,he],hv',hc',hr.trans (Reader.pop_conservation _ _ _ hpop)⟩

def eraseMargins (B N L R : ℕ) (source : File) : Option Result := do
  let afterLeft ← skip L (Reader.fromDisk source)
  let copied ← StreamCopy.run B N ⟨afterLeft,Writer.empty⟩
  let afterRight ← skip R copied.source
  return (copied.target.finish,afterRight.reads+copied.target.finish.length)

theorem eraseMargins_correct (B : ℕ) (hB : 0 < B) (left xs right : List Bit)
    (source : File) (hv : (Reader.fromDisk source).Valid B)
    (hf : source.flatten=left++xs++right) :
    eraseMargins B xs.length left.length right.length source=
      some (pack B hB xs,source.length+(xs.length+B-1)/B) := by
  obtain ⟨afterLeft,hl,hvl,hcl,hrl⟩ := skip_correct B left (xs++right) (Reader.fromDisk source) hv
    (by simpa [Reader.contents,Reader.fromDisk,List.append_assoc] using hf)
  obtain ⟨copied,hcopy,hvc,hcc,hout,hrc⟩ := copy_prefix B xs right
    ⟨afterLeft,Writer.empty⟩ ⟨hvl,Writer.empty_valid B hB⟩ hcl
  obtain ⟨afterRight,hr,hvr,hcr,hrr⟩ := skip_correct B right [] copied.source hvc.1 (by simpa using hcc)
  have hd := Reader.empty_contents_disk B afterRight hvr hcr
  have hreads : afterRight.reads=source.length := by
    have h := hrr.trans (hrc.trans hrl)
    simpa [Reader.fromDisk,hd] using h
  have he : copied.target.finish=pack B hB xs := by
    rw [DiskStreamPass.writer_finish_eq_pack B hB _ hvc.2,hout]
    simp [Writer.contents,Writer.empty]
  simp [eraseMargins,hl,hcopy,hr,he,hreads,pack_count]

/-- The fourth batch reads the shifted scan's actual output; the final
scan removes margins from that batch's actual returned file. -/
def halfRound (B N h : ℕ) (left right : ℕ → Bit)
    (batch : File → Option Result) (source : File) : Option Result := do
  let shifted ← addMargins B N h h left right source
  let middle ← batch shifted.1
  let result ← eraseMargins B N h h middle.1
  return (result.1,shifted.2+middle.2+result.2)

/-- Exactly two complete reads and two complete writes are charged around
the fourth batch. Its own returned cost is added, not replaced by a bound.
The output margins may have changed during sorting; only their lengths are
used by the erasure program. -/
theorem halfRound_correct (B : ℕ) (hB : 0 < B) (h : ℕ) (left right : ℕ → Bit)
    (xs ys lo ro : List Bit) (hn : ys.length=xs.length)
    (hl : lo.length=h) (hr : ro.length=h)
    (batch : File → Option Result) (batchCost : ℕ)
    (hbatch : batch (pack B hB (paddingValues h 0 left++xs++paddingValues h 0 right))=
      some (pack B hB (lo++ys++ro),batchCost)) :
    halfRound B xs.length h left right batch (pack B hB xs)=
      some (pack B hB ys,
        2*((xs.length+B-1)/B)+2*((h+xs.length+h+B-1)/B)+batchCost) := by
  have hi := addMargins_correct B hB h h left right xs (pack B hB xs)
    (pack_reader_valid B hB xs) (flatten_pack B hB xs)
  have he := eraseMargins_correct B hB lo ys ro (pack B hB (lo++ys++ro))
    (pack_reader_valid B hB _) (flatten_pack B hB _)
  rw [hn,hl,hr] at he
  simp only [pack_count,List.length_append,hn,hl,hr] at hi he
  simp only [List.append_assoc] at hi he hbatch
  simp [halfRound,hi,hbatch,he]
  omega

end
end CodedSorting.PhysicalLocalSortScan
end PhysicalLocalSortScan

section PhysicalLocalSortEncoding
/-! Row-major record encoding shared by the actual local-sort scans.
All bits of one record are consecutive, in their original word encoding.
The bit-list expressions are specifications, not runtime reconstruction. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalLocalSortEncoding
open Circuit PhysicalLocalSortScan
variable {α : Type*} {w m n : ℕ}

def encodeList (code : α → Fin w → Bit) (xs : List α) : List Bit :=
  xs.flatMap (fun x => List.ofFn (code x))

def bitList (code : α → Fin w → Bit) (f : Fin n → α) : List Bit :=
  encodeList code (List.ofFn f)

@[simp] theorem encodeList_append (code : α → Fin w → Bit) (xs ys : List α) :
    encodeList code (xs++ys)=encodeList code xs++encodeList code ys := by
  simp only [encodeList,List.flatMap_append]

@[simp] theorem encodeList_length (code : α → Fin w → Bit) (xs : List α) :
    (encodeList code xs).length=xs.length*w := by
  induction xs with
  | nil => simp [encodeList]
  | cons a xs ih => simpa [encodeList,Nat.add_mul,Nat.add_comm] using congrArg (fun z => w+z) ih

@[simp] theorem bitList_length (code : α → Fin w → Bit) (f : Fin n → α) :
    (bitList code f).length=n*w := by simp [bitList]

theorem bitList_fin_append (code : α → Fin w → Bit) (f : Fin m → α) (g : Fin n → α) :
    bitList code (Fin.append f g)=bitList code f++bitList code g := by
  simp [bitList]

def sentinel (hw : 0 < w) (code : α → Fin w → Bit) (a : α) : ℕ → Bit :=
  fun i => code a ⟨i%w,Nat.mod_lt _ hw⟩

theorem padding_sentinel (n : ℕ) (hw : 0 < w) (code : α → Fin w → Bit) (a : α) :
    paddingValues (n*w) 0 (sentinel hw code a)=encodeList code (List.replicate n a) := by
  have he : encodeList code (List.replicate n a)=
      (List.replicate n (List.ofFn (code a))).flatten := by
    simp [encodeList,List.flatMap]
  rw [he,← List.ofFn_fin_repeat]
  apply List.ext_getElem
  · simp [paddingValues]
  · intro i hi hi'
    rw [List.getElem_ofFn]
    simp [paddingValues,sentinel,Fin.repeat,Fin.modNat]

theorem bitList_const (n : ℕ) (code : α → Fin w → Bit) (a : α) :
    bitList code (fun _ : Fin n => a)=encodeList code (List.replicate n a) := by
  simp [bitList]

end CodedSorting.PhysicalLocalSortEncoding
end PhysicalLocalSortEncoding

section PhysicalLocalSortInitial
/-! Decomposition of a record list for extracting its final prefix. 
-/
set_option autoImplicit false
namespace CodedSorting.PhysicalLocalSortInitial
open Circuit PhysicalRecursiveExchange PhysicalExchangeRecursion
open BucketMachine BucketReader RecursiveColumnsort
noncomputable section

variable {α : Type*}

/-- Records removed by the final scan, in their actual output order. -/
def tail {n N : ℕ} (h : n ≤ N) (f : Fin N → α) : Fin (N-n) → α :=
  fun i => f ⟨n+i.val, by have := i.isLt; omega⟩

/-- The finite trim operation is exactly a prefix of the returned record
list; it does not inspect or synthesize records. -/
theorem trim_append_tail {n N : ℕ} (h : n ≤ N) (f : Fin N → α) :
    List.ofFn f = List.ofFn (trim h f) ++ List.ofFn (tail h f) := by
  have he : N = n+(N-n) := by omega
  rw [List.ofFn_congr he, List.ofFn_add]
  congr 1

end
end CodedSorting.PhysicalLocalSortInitial
end PhysicalLocalSortInitial

section PhysicalLocalSortPadding
/-! The half-column scan produces exactly the existing fourth Columnsort
batch input, including both sentinel encodings and every within-record bit.
The equalities below describe one sequential file, not separate columns
that can be repacked for free. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalLocalSortPadding
open Circuit PhysicalRecursiveExchange PhysicalExchangeRecursion
open BucketMachine BucketReader StreamCopy RecursiveColumnsort
open PhysicalLocalSortScan PhysicalLocalSortEncoding
noncomputable section
variable {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]

def flattenColumns (s r : ℕ) (f : Fin s → Fin r → α) : Fin (s*r) → α :=
  fun i => f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

def fourthInput (s r h : ℕ) (three : Fin s → Fin r → α) : Fin (s+1) → Fin r → α :=
  fun c => gridInput r (-(h : ℤ)) (gridTape s r 0 three) c

theorem flatten_gridInput (s r : ℕ) (offset : ℤ) (f : ℤ → α) :
    flattenColumns s r (fun c => gridInput r offset f c) =
      fun i : Fin (s*r) => f (offset+(i : ℤ)) := by
  funext i
  unfold flattenColumns gridInput
  change f (offset+((finProdFinEquiv.symm i).1 : ℤ)*r+((finProdFinEquiv.symm i).2 : ℤ))=
    f (offset+(i : ℤ))
  apply congrArg f
  have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)
  change (finProdFinEquiv.symm i).2.val+r*(finProdFinEquiv.symm i).1.val=i.val at h
  have hz : ((finProdFinEquiv.symm i).2 : ℤ)+(r : ℤ)*((finProdFinEquiv.symm i).1 : ℤ)=(i : ℤ) := by
    exact_mod_cast h
  linarith

def shiftedRecords (s r h : ℕ) (three : Fin s → Fin r → α) : Fin ((s+1)*r) → α :=
  fun i => gridTape s r 0 three (-(h : ℤ)+(i : ℤ))

theorem fourth_flatten (s r h : ℕ) (three : Fin s → Fin r → α) :
    flattenColumns (s+1) r (fourthInput s r h three)=shiftedRecords s r h three :=
  flatten_gridInput (s+1) r (-(h : ℤ)) _

theorem shifted_records (s r h : ℕ) (hr : r=2*h) (three : Fin s → Fin r → α) :
    List.ofFn (shiftedRecords s r h three)=
      List.replicate h (⊥ : α)++List.ofFn (flattenColumns s r three)++List.replicate h (⊤ : α) := by
  have he : (s+1)*r=(h+s*r)+h := by rw [hr]; ring
  have hf : (fun i : Fin ((h+s*r)+h) => shiftedRecords s r h three (Fin.cast he.symm i))=
      Fin.append (Fin.append (fun _ : Fin h => (⊥ : α)) (flattenColumns s r three))
        (fun _ : Fin h => (⊤ : α)) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro k
        simp only [shiftedRecords,Fin.coe_cast,Fin.coe_castAdd,Fin.append_left]
        exact (gridTape_bounds s r 0 three).1 _ (by have := k.isLt; omega)
      · intro k
        simp only [shiftedRecords,Fin.coe_cast,Fin.coe_castAdd,Fin.coe_natAdd,
          Fin.append_left,Fin.append_right]
        have hz : -(h : ℤ)+(h+(k : ℕ) : ℕ)=(k : ℤ) := by omega
        rw [hz]
        simpa [flattenColumns] using gridTape_at_fin s r 0 three k
    · intro k
      simp only [shiftedRecords,Fin.coe_cast,Fin.coe_natAdd,Fin.append_right]
      exact (gridTape_bounds s r 0 three).2 _ (by omega)
  rw [List.ofFn_congr he,hf,List.ofFn_fin_append,List.ofFn_fin_append]
  simp

theorem fourth_bitList (s r h w : ℕ) (hr : r=2*h) (hw : 0<w)
    (code : α → Fin w → Bit) (three : Fin s → Fin r → α) :
    bitList code (flattenColumns (s+1) r (fourthInput s r h three))=
      paddingValues (h*w) 0 (sentinel hw code ⊥)++
        bitList code (flattenColumns s r three)++paddingValues (h*w) 0 (sentinel hw code ⊤) := by
  rw [fourth_flatten]
  unfold bitList
  rw [shifted_records s r h hr,padding_sentinel,padding_sentinel,
    encodeList_append,encodeList_append]

/-- The same Reader/Writer scan whose transfers are counted returns the
encoded input of every fourth-batch column, in column-major order. -/
theorem half_shift_file (s r h w B : ℕ) (hr : r=2*h) (hw : 0<w) (hB : 0<B)
    (code : α → Fin w → Bit) (three : Fin s → Fin r → α)
    (source : File) (hv : (Reader.fromDisk source).Valid B)
    (hf : source.flatten=bitList code (flattenColumns s r three)) :
    addMargins B (s*r*w) (h*w) (h*w) (sentinel hw code ⊥) (sentinel hw code ⊤) source=
      some (pack B hB (bitList code (flattenColumns (s+1) r (fourthInput s r h three))),
        source.length+((s+1)*r*w+B-1)/B) := by
  have hs := addMargins_correct B hB (h*w) (h*w) (sentinel hw code ⊥) (sentinel hw code ⊤)
    (bitList code (flattenColumns s r three)) source hv hf
  rw [bitList_length,← fourth_bitList s r h w hr hw code three] at hs
  have he : h*w+s*r*w+h*w=(s+1)*r*w := by rw [hr]; ring
  simpa only [he] using hs

def unshiftedRecords (s r h : ℕ) (four : Fin (s+1) → Fin r → α) : Fin (s*r) → α :=
  fun i => gridTape (s+1) r (-(h : ℤ)) four (i : ℤ)

theorem unshifted_at (s r h : ℕ) (hr : r=2*h) (four : Fin (s+1) → Fin r → α)
    (i : Fin (s*r)) :
    unshiftedRecords s r h four i=
      flattenColumns (s+1) r four (Fin.cast (show (h+s*r)+h=(s+1)*r by rw [hr]; ring)
        ((i.natAdd h).castAdd h)) := by
  let he : (h+s*r)+h=(s+1)*r := by rw [hr]; ring
  let j : Fin ((s+1)*r) := Fin.cast he ((i.natAdd h).castAdd h)
  have hg := gridTape_at_fin (s+1) r (-(h : ℤ)) four j
  have hz : -(h : ℤ)+(j : ℤ)=(i : ℤ) := by
    dsimp only [j]
    simp only [Fin.coe_cast,Fin.coe_castAdd,Fin.coe_natAdd]
    omega
  rw [hz] at hg
  exact hg

/-- Erasure discards the actual first and last half columns after the
fourth batch, regardless of their contents. The retained middle is exactly
the finite output expression in `fourRounds`. -/
theorem unshifted_bitList_split (s r h w : ℕ) (hr : r=2*h)
    (code : α → Fin w → Bit) (four : Fin (s+1) → Fin r → α) :
    ∃ left right : List Bit, left.length=h*w ∧ right.length=h*w ∧
      bitList code (flattenColumns (s+1) r four)=
        left++bitList code (unshiftedRecords s r h four)++right := by
  let he : (s+1)*r=(h+s*r)+h := by rw [hr]; ring
  let f := flattenColumns (s+1) r four
  let left : Fin h → α := fun i => f (Fin.cast he.symm ((i.castAdd (s*r)).castAdd h))
  let right : Fin h → α := fun i => f (Fin.cast he.symm (i.natAdd (h+s*r)))
  have hm : (fun i : Fin (s*r) => f (Fin.cast he.symm ((i.natAdd h).castAdd h)))=
      unshiftedRecords s r h four := by
    funext i
    exact (unshifted_at s r h hr four i).symm
  have hsplit : List.ofFn f=List.ofFn left++List.ofFn (unshiftedRecords s r h four)++List.ofFn right := by
    rw [List.ofFn_congr he,List.ofFn_add,List.ofFn_add,hm]
  refine ⟨bitList code left,bitList code right,bitList_length _ _,bitList_length _ _,?_⟩
  change encodeList code (List.ofFn f)=_
  rw [hsplit,encodeList_append,encodeList_append]
  rfl

theorem half_unshift_file (s r h w B : ℕ) (hr : r=2*h) (hB : 0<B)
    (code : α → Fin w → Bit) (four : Fin (s+1) → Fin r → α)
    (source : File) (hv : (Reader.fromDisk source).Valid B)
    (hf : source.flatten=bitList code (flattenColumns (s+1) r four)) :
    eraseMargins B (s*r*w) (h*w) (h*w) source=
      some (pack B hB (bitList code (unshiftedRecords s r h four)),
        source.length+(s*r*w+B-1)/B) := by
  obtain ⟨left,right,hl,hright,he⟩ := unshifted_bitList_split s r h w hr code four
  have hs := eraseMargins_correct B hB left (bitList code (unshiftedRecords s r h four)) right source hv
    (hf.trans he)
  simpa only [bitList_length,hl,hright] using hs

/-- A fourth-batch implementation needs only its actual execution on the
existing `gridInput`; all sentinel encoding and trimming obligations are
discharged here rather than left as separate callback assumptions. -/
theorem halfRound_columnsort (s r h w B : ℕ) (hr : r=2*h) (hw : 0<w) (hB : 0<B)
    (code : α → Fin w → Bit) (three : Fin s → Fin r → α)
    (four : Fin (s+1) → Fin r → α) (batch : File → Option Result) (batchCost : ℕ)
    (hbatch : batch (pack B hB (bitList code (flattenColumns (s+1) r (fourthInput s r h three))))=
      some (pack B hB (bitList code (flattenColumns (s+1) r four)),batchCost)) :
    halfRound B (s*r*w) (h*w) (sentinel hw code ⊥) (sentinel hw code ⊤) batch
      (pack B hB (bitList code (flattenColumns s r three)))=
      some (pack B hB (bitList code (unshiftedRecords s r h four)),
        2*((s*r*w+B-1)/B)+2*(((s+1)*r*w+B-1)/B)+batchCost) := by
  obtain ⟨left,right,hl,hright,he⟩ := unshifted_bitList_split s r h w hr code four
  rw [fourth_bitList s r h w hr hw code three,he] at hbatch
  have hs := halfRound_correct B hB (h*w) (sentinel hw code ⊥) (sentinel hw code ⊤)
    (bitList code (flattenColumns s r three)) (bitList code (unshiftedRecords s r h four)) left right
    (by simp) hl hright batch batchCost hbatch
  simp only [bitList_length] at hs
  have hsize : h*w+s*r*w+h*w=(s+1)*r*w := by rw [hr]; ring
  simpa only [hsize] using hs

end
end CodedSorting.PhysicalLocalSortPadding
end PhysicalLocalSortPadding

section PhysicalLocalSortBoundary
/-! The caller's existing file is top-padded by an actual scan, and the
returned sorted file is prefix-trimmed by an actual scan. These endpoints
are the same `pad`, `paddedInput` and `trim` used by `nodeRun`. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalLocalSortBoundary
open Circuit PhysicalRecursiveExchange PhysicalExchangeRecursion
open BucketMachine BucketReader StreamCopy RecursiveColumnsort
open PhysicalLocalSortScan PhysicalLocalSortEncoding PhysicalLocalSortInitial
noncomputable section
variable {α : Type*} [LinearOrder α] [OrderTop α]

theorem bitList_pad {n N w : ℕ} (h : n≤N) (hw : 0<w)
    (code : α → Fin w → Bit) (f : Fin n → α) :
    bitList code (pad (N:=N) f)=bitList code f++
      paddingValues ((N-n)*w) 0 (sentinel hw code ⊤) := by
  unfold bitList
  rw [pad_ofFn h,encodeList_append,padding_sentinel]

theorem initial_top_file {n N w : ℕ} (h : n≤N) (hw : 0<w) (B : ℕ) (hB : 0<B)
    (code : α → Fin w → Bit) (f : Fin n → α) (source : File)
    (hv : (Reader.fromDisk source).Valid B) (hf : source.flatten=bitList code f) :
    addMargins B (n*w) 0 ((N-n)*w) (sentinel hw code ⊤) (sentinel hw code ⊤) source=
      some (pack B hB (bitList code (pad (N:=N) f)),source.length+(N*w+B-1)/B) := by
  have hs := addMargins_correct B hB 0 ((N-n)*w) (sentinel hw code ⊤) (sentinel hw code ⊤)
    (bitList code f) source hv hf
  have hz : paddingValues 0 0 (sentinel hw code ⊤)=[] := rfl
  rw [bitList_length,hz,List.nil_append,← bitList_pad h hw code f] at hs
  have he : n*w+(N-n)*w=N*w := by rw [← Nat.add_mul,Nat.add_sub_of_le h]
  simpa only [Nat.zero_add,he] using hs

theorem initial_paddedInput_file [OrderBot α] {n w : ℕ} (hw : 0<w) (B : ℕ) (hB : 0<B)
    (code : α → Fin w → Bit) (f : Fin n → α) (source : File)
    (hv : (Reader.fromDisk source).Valid B) (hf : source.flatten=bitList code f) :
    addMargins B (n*w) 0 ((paddedLength n-n)*w) (sentinel hw code ⊤) (sentinel hw code ⊤) source=
      some (pack B hB (bitList code (Columnsort.flattenKeys ((LocalShape.sizeChoice n)^2)
        (LocalShape.sizeChoice n) 1 (paddedInput f))),
        source.length+(paddedLength n*w+B-1)/B) := by
  rw [flatten_paddedInput]
  exact initial_top_file (paddedLength_ge n) hw B hB code f source hv hf

theorem final_trim_file {n N w : ℕ} (h : n≤N) (B : ℕ) (hB : 0<B)
    (code : α → Fin w → Bit) (f : Fin N → α) (source : File)
    (hv : (Reader.fromDisk source).Valid B) (hf : source.flatten=bitList code f) :
    eraseMargins B (n*w) 0 ((N-n)*w) source=
      some (pack B hB (bitList code (trim h f)),source.length+(n*w+B-1)/B) := by
  have he : bitList code f=bitList code (trim h f)++bitList code (tail h f) := by
    unfold bitList
    rw [trim_append_tail h f,encodeList_append]
  have hs := eraseMargins_correct B hB [] (bitList code (trim h f)) (bitList code (tail h f))
    source hv (by simpa only [List.nil_append] using hf.trans he)
  simpa only [bitList_length,List.length_nil] using hs

end
end CodedSorting.PhysicalLocalSortBoundary
end PhysicalLocalSortBoundary

section PhysicalLocalSortLayout
/-! Exact equality between the physical exchange's four-field record view
and the ordinary column-major serialized file. No rearrangement is charged
or performed by these equalities: every bit has the same integer address. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalLocalSortLayout
open Circuit Address PhysicalRecursiveExchange
open BucketMachine RecursiveColumnsort ColumnsortExchange
open PhysicalSortingExchangeLayout PhysicalLocalSortTranspose PhysicalLocalSortInverse
open PhysicalLocalSortEncoding PhysicalLocalSortPadding
noncomputable section
variable {α : Type*} {A : Type} {n m w : ℕ}

theorem bitList_numeric (code : α → Fin w → Bit) (f : Fin n → α) :
    bitList code f=List.ofFn (fun i : Fin (n*w) =>
      code (f (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2) := by
  rw [List.ofFn_mul]
  unfold bitList encodeList
  rw [List.flatMap,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have he : (⟨i.val*w+j.val,by have := i.isLt; have := j.isLt; nlinarith⟩ : Fin (n*w))=
      finProdFinEquiv (i,j) := by apply Fin.ext; change i.val*w+j.val=j.val+w*i.val; ring
  rw [he,Equiv.symm_apply_apply]

theorem bitList_cast (h : m=n) (code : α → Fin w → Bit) (f : Fin n → α) :
    bitList code (fun i : Fin m => f (finCongr h i))=bitList code f := by
  subst n
  rfl

theorem represented_product (e : A ≃ Fin n) (B : ℕ) (hB : 0<B)
    (code : α → Fin w → Bit) (f : Fin n → α) :
    represented ((Equiv.prodCongr e (Equiv.refl (Fin w))).trans finProdFinEquiv) B hB
      (fun a : A × Fin w => code (f (e a.1)) a.2)=pack B hB (bitList code f) := by
  rw [bitList_numeric]
  apply congrArg (pack B hB)
  apply congrArg List.ofFn
  funext i
  change code (f (e (e.symm (finProdFinEquiv.symm i).1))) (finProdFinEquiv.symm i).2=_
  rw [Equiv.apply_symm_apply]

theorem firstColumn_address (s : ℕ) (x : Fields s) :
    finProdFinEquiv (x.1,firstRow s x)=
      finCongr (show s^4=s*(s^2*s*1) by ring) (encode s x) := by
  apply Fin.ext
  rw [finCongr_apply_coe,encode_val]
  change x.2.2.2.val+s*(x.2.2.1.val+s*x.2.1.val)+(s^2*s*1)*x.1.val=_
  ring

theorem secondColumn_address (s : ℕ) (x : Fields s) :
    finProdFinEquiv (x.1,secondRow s x)=
      finCongr (show s^4=s*(s*(s^2*1)) by ring) (encode s x) := by
  apply Fin.ext
  rw [finCongr_apply_coe,encode_val]
  change x.2.2.2.val+s*x.2.2.1.val+(s^2*1)*x.2.1.val+(s*(s^2*1))*x.1.val=_
  ring

variable [LinearOrder α] [OrderBot α] [OrderTop α]

theorem first_file (s w B : ℕ) (hB : 0<B) (code : α → Fin w → Bit)
    (one : Fin s → Fin (s^2*s*1) → α) :
    represented (recordLayout s w) B hB (firstValues s w (fun c i => code (one c i)))=
      pack B hB (bitList code (flattenColumns s (s^2*s*1) one)) := by
  let h : s^4=s*(s^2*s*1) := by ring
  let f : Fin (s^4) → α := fun i => flattenColumns s (s^2*s*1) one (finCongr h i)
  have hf : firstValues s w (fun c i => code (one c i))=
      fun a : RecordAddress s w => code (f (encode s a.1)) a.2 := by
    funext a
    dsimp only [f]
    rw [← firstColumn_address]
    simp only [flattenColumns,Equiv.symm_apply_apply,firstValues]
  rw [hf]
  rw [show recordLayout s w=(Equiv.prodCongr (encode s) (Equiv.refl (Fin w))).trans finProdFinEquiv from rfl]
  rw [represented_product,bitList_cast]

theorem second_file (s w B : ℕ) (hB : 0<B) (code : α → Fin w → Bit)
    (two : Fin s → Fin (s*(s^2*1)) → α) :
    represented (recordLayout s w) B hB (returnedValues s w code two)=
      pack B hB (bitList code (flattenColumns s (s*(s^2*1)) two)) := by
  let h : s^4=s*(s*(s^2*1)) := by ring
  let f : Fin (s^4) → α := fun i => flattenColumns s (s*(s^2*1)) two (finCongr h i)
  have hf : returnedValues s w code two=
      fun a : RecordAddress s w => code (f (encode s a.1)) a.2 := by
    funext a
    dsimp only [f]
    rw [← secondColumn_address]
    simp only [flattenColumns,Equiv.symm_apply_apply,returnedValues]
  rw [hf]
  rw [show recordLayout s w=(Equiv.prodCongr (encode s) (Equiv.refl (Fin w))).trans finProdFinEquiv from rfl]
  rw [represented_product,bitList_cast]

theorem secondInput_file (s w B : ℕ) (hB : 0<B) (code : α → Fin w → Bit)
    (one : Fin s → Fin (s^2*s*1) → α) :
    represented (recordLayout s w) B hB (secondValues s w (fun c i => code (one c i)))=
      pack B hB (bitList code (flattenColumns s (s*(s^2*1)) (secondInput (s^2) s one))) :=
  second_file s w B hB code (secondInput (s^2) s one)

theorem thirdInput_file (s w B : ℕ) (hB : 0<B) (code : α → Fin w → Bit)
    (two : Fin s → Fin (s*(s^2*1)) → α) :
    represented (recordLayout s w) B hB (thirdValues s w code two)=
      pack B hB (bitList code (flattenColumns s (s^2*s*1)
        (fun c => gridInput (s^2*s*1) 0 (afterTwoTape (s^2) s two) c))) :=
  first_file s w B hB code (fun c => gridInput (s^2*s*1) 0 (afterTwoTape (s^2) s two) c)

end
end CodedSorting.PhysicalLocalSortLayout
end PhysicalLocalSortLayout

section PhysicalLocalSortLeafCodec
/-! A RAM adapter for sorting a serialized column.  Its executable input is
the list of bits in RAM; decoding reads consecutive record-width slices. -/
set_option autoImplicit false

namespace CodedSorting.PhysicalLocalSortLeafCodec

open Circuit PhysicalLocalSortEncoding PhysicalLocalSortLayout

variable {α : Type*} {v n : ℕ}

def decodeColumn (n : ℕ) (decode : (Fin v → Bit) → α) (bits : List Bit) : Fin n → α :=
  fun i => decode (fun j => bits.getD (i.val * v + j.val) 0)

theorem decodeColumn_bitList (code : α → Fin v → Bit)
    (decode : (Fin v → Bit) → α) (hdecode : ∀ a, decode (code a) = a)
    (f : Fin n → α) : decodeColumn n decode (bitList code f) = f := by
  funext i
  change decode (fun j => (bitList code f).getD (i.val * v + j.val) 0) = f i
  rw [← hdecode (f i)]
  apply congrArg decode
  funext j
  rw [bitList_numeric]
  have hi : i.val * v + j.val < n * v := by
    have := i.isLt
    have := j.isLt
    nlinarith
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using hi), Option.getD_some, List.getElem_ofFn]
  have he : (⟨i.val * v + j.val, hi⟩ : Fin (n * v)) = finProdFinEquiv (i, j) := by
    apply Fin.ext
    change i.val * v + j.val = j.val + v * i.val
    ring
  rw [he, Equiv.symm_apply_apply]

variable [LinearOrder α]

def ramSort (n : ℕ) (code : α → Fin v → Bit)
    (decode : (Fin v → Bit) → α) (bits : List Bit) : List Bit :=
  bitList code (Columnsort.sortColumn (decodeColumn n decode bits))

theorem ramSort_bitList (code : α → Fin v → Bit)
    (decode : (Fin v → Bit) → α) (hdecode : ∀ a, decode (code a) = a)
    (f : Fin n → α) :
    ramSort n code decode (bitList code f) = bitList code (Columnsort.sortColumn f) := by
  rw [ramSort, decodeColumn_bitList code decode hdecode]

@[simp] theorem ramSort_length (n : ℕ) (code : α → Fin v → Bit)
    (decode : (Fin v → Bit) → α) (bits : List Bit) :
    (ramSort n code decode bits).length = n * v := by
  simp [ramSort]

end CodedSorting.PhysicalLocalSortLeafCodec
end PhysicalLocalSortLeafCodec

section PhysicalLocalSortNode
/-! All file movement in one scalar Columnsort node. A single batch
implementation is invoked four times on the actual preceding output file.
The theorem below requires those four concrete batch executions; it does
not assert an implementation or correctness theorem for recursive batches.
Padding, all six exchanges, the half shift and both trims are implemented
here, with their returned costs accumulated from the same execution. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace CodedSorting.PhysicalLocalSortNode
open Circuit Address RecursiveExchange PhysicalRecursiveExchange PhysicalExchangeRecursion
open BucketMachine BucketReader StreamCopy RecursiveColumnsort ColumnsortExchange
open PhysicalSortingExchangeLayout PhysicalSortingExchange PhysicalLocalSortTranspose
open PhysicalLocalSortInverse PhysicalLocalSortEncoding PhysicalLocalSortPadding
open PhysicalLocalSortLayout PhysicalLocalSortBoundary
noncomputable section

def rows (s : ℕ) : ℕ := s^2*s*1

def scanCharge (B n s w : ℕ) : ℕ :=
  2*((n*w+B-1)/B)+4*((s*rows s*w+B-1)/B)+2*(((s+1)*rows s*w+B-1)/B)

def runNode (base cutoff B : ℕ) (hB : 0<B) (n t h w : ℕ)
    (bottom top : ℕ → Bit) (batch : ℕ → ℕ → File → Option Result)
    (source : File) : Option Result := do
  let s := 2^t
  let padded ← PhysicalLocalSortScan.addMargins B (n*w) 0 ((s*rows s-n)*w) top top source
  let one ← batch s (rows s) padded.1
  let two ← aroundBatch base cutoff B hB t w (batch s (s*(s^2*1))) one.1
  let three ← batch s (rows s) two.1
  let four ← PhysicalLocalSortScan.halfRound B (s*rows s*w) (h*w) bottom top
    (batch (s+1) (rows s)) three.1
  let result ← PhysicalLocalSortScan.eraseMargins B (n*w) 0 ((s*rows s-n)*w) four.1
  return (result.1,padded.2+one.2+two.2+three.2+four.2+result.2)

variable {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]

def initialColumns {n : ℕ} (s : ℕ) (f : Fin n → α) : Fin s → Fin (rows s) → α :=
  fun c i => pad (N:=s*rows s) f (finProdFinEquiv (c,i))

theorem initial_flat {n : ℕ} (s : ℕ) (f : Fin n → α) :
    flattenColumns s (rows s) (initialColumns s f)=pad (N:=s*rows s) f := by
  funext i
  change pad f (finProdFinEquiv (finProdFinEquiv.symm i))=pad f i
  rw [Equiv.apply_symm_apply]

def thirdColumns (s : ℕ) (two : Fin s → Fin (s*(s^2*1)) → α) : Fin s → Fin (rows s) → α :=
  fun c => gridInput (rows s) 0 (afterTwoTape (s^2) s two) c

theorem original_paddedInput {n : ℕ} (f : Fin n → α) :
    initialColumns (LocalShape.sizeChoice n) f=paddedInput f := by
  funext c i
  rfl

/-- Substituting the existing sorter's four batches yields precisely its
original `fourRounds` output, including the final half-column removal. -/
theorem original_fourRounds (s h w : ℕ) (code : α → Fin w → Bit) (sorter : Sorter α)
    (input : Fin s → Fin (rows s) → α) :
    let one := fun c => (sorter (rows s) (input c)).output
    let two := fun c => (sorter (s*(s^2*1)) (secondInput (s^2) s one c)).output
    let three := fun c => (sorter (rows s) (thirdColumns s two c)).output
    let four := fun c => (sorter (rows s) (fourthInput s (rows s) h three c)).output
    bitList code (fourRounds sorter (s^2) s h input).output=
      bitList code (unshiftedRecords s (rows s) h four) := by
  let one := fun c => (sorter (rows s) (input c)).output
  let two := fun c => (sorter (s*(s^2*1)) (secondInput (s^2) s one c)).output
  let three := fun c => (sorter (rows s) (thirdColumns s two c)).output
  let four := fun c => (sorter (rows s) (fourthInput s (rows s) h three c)).output
  change bitList code (fourRounds sorter (s^2) s h input).output=
    bitList code (unshiftedRecords s (rows s) h four)
  exact bitList_cast (show s*s^2*(s*1)=s*rows s by unfold rows; ring) code
    (unshiftedRecords s (rows s) h four)

/-- The complete padded-and-trimmed endpoint is the existing node result,
with no change in the order or encoding of the retained records. -/
theorem original_nodeRun (n w : ℕ) (code : α → Fin w → Bit) (sorter : Sorter α)
    (f : Fin n → α) (hpad : n≤LocalShape.sizeChoice n*rows (LocalShape.sizeChoice n)) :
    let s := LocalShape.sizeChoice n
    let h := LocalShape.columnLength n/2
    let one := fun c => (sorter (rows s) (initialColumns s f c)).output
    let two := fun c => (sorter (s*(s^2*1)) (secondInput (s^2) s one c)).output
    let three := fun c => (sorter (rows s) (thirdColumns s two c)).output
    let four := fun c => (sorter (rows s) (fourthInput s (rows s) h three c)).output
    bitList code (nodeRun sorter n f).output=
      bitList code (trim hpad (unshiftedRecords s (rows s) h four)) := by
  rfl

theorem runNode_movement (base cutoff B : ℕ) (hB : 0<B) (hb : 0<base)
    (hstartup : (radix^base*radix^base)*B≤cutoff+B)
    (n t h w : ℕ) (hw : 0<w) (hpad : n≤(2^t)*rows (2^t)) (hheight : rows (2^t)=2*h)
    (code : α → Fin w → Bit) (f : Fin n → α)
    (one : Fin (2^t) → Fin (rows (2^t)) → α)
    (two : Fin (2^t) → Fin ((2^t)*((2^t)^2*1)) → α)
    (three : Fin (2^t) → Fin (rows (2^t)) → α)
    (four : Fin (2^t+1) → Fin (rows (2^t)) → α)
    (batch : ℕ → ℕ → File → Option Result) (c1 c2 c3 c4 : ℕ)
    (h1 : batch (2^t) (rows (2^t))
      (pack B hB (bitList code (flattenColumns (2^t) (rows (2^t)) (initialColumns (2^t) f))))=
        some (pack B hB (bitList code (flattenColumns (2^t) (rows (2^t)) one)),c1))
    (h2 : batch (2^t) ((2^t)*((2^t)^2*1))
      (pack B hB (bitList code (flattenColumns (2^t) ((2^t)*((2^t)^2*1))
        (secondInput ((2^t)^2) (2^t) one))))=
        some (pack B hB (bitList code (flattenColumns (2^t) ((2^t)*((2^t)^2*1)) two)),c2))
    (h3 : batch (2^t) (rows (2^t))
      (pack B hB (bitList code (flattenColumns (2^t) (rows (2^t)) (thirdColumns (2^t) two))))=
        some (pack B hB (bitList code (flattenColumns (2^t) (rows (2^t)) three)),c3))
    (h4 : batch (2^t+1) (rows (2^t))
      (pack B hB (bitList code (flattenColumns (2^t+1) (rows (2^t))
        (fourthInput (2^t) (rows (2^t)) h three))))=
        some (pack B hB (bitList code (flattenColumns (2^t+1) (rows (2^t)) four)),c4)) :
    ∃ out,
      runNode base cutoff B hB n t h w (sentinel hw code ⊥) (sentinel hw code ⊤)
        batch (pack B hB (bitList code f))=some out ∧
      out.1=pack B hB (bitList code (trim hpad (unshiftedRecords (2^t) (rows (2^t)) h four))) ∧
      out.2≤c1+c2+c3+c4+charge base cutoff B t w forwardSwaps+
        charge base cutoff B t w backwardSwaps+scanCharge B n (2^t) w := by
  let s := 2^t
  let r := rows s
  have hp := initial_top_file hpad hw B hB code f (pack B hB (bitList code f))
    (pack_reader_valid B hB _) (flatten_pack B hB _)
  rw [← initial_flat (2^t) f] at hp
  simp only [pack_count,bitList_length] at hp
  let mid : Result := (pack B hB (bitList code (flattenColumns s (s*(s^2*1)) two)),c2)
  have hmid : mid.1=represented (recordLayout s w) B hB (returnedValues s w code two) :=
    (second_file s w B hB code two).symm
  have hbatch : batch s (s*(s^2*1))
      (represented (recordLayout s w) B hB (secondValues s w (fun c i => code (one c i))))=some mid := by
    rw [secondInput_file]
    exact h2
  obtain ⟨ex,hex,hout,hcost⟩ := aroundBatch_correct base cutoff B hB hb hstartup t w hw
    (fun c i => code (one c i)) (batch s (s*(s^2*1))) mid
    (returnedValues s w code two) hbatch hmid
  rw [first_file] at hex
  rw [backward_is_thirdInput,thirdInput_file] at hout
  change aroundBatch base cutoff B hB t w (batch s (s*(s^2*1)))
    (pack B hB (bitList code (flattenColumns s r one)))=some ex at hex
  change ex.1=pack B hB (bitList code (flattenColumns s r (thirdColumns s two))) at hout
  have hhalf := halfRound_columnsort s r h w B hheight hw hB code three four
    (batch (s+1) r) c4 h4
  have ht := final_trim_file hpad B hB code (unshiftedRecords s r h four)
    (pack B hB (bitList code (unshiftedRecords s r h four)))
    (pack_reader_valid B hB _) (flatten_pack B hB _)
  simp only [pack_count,bitList_length] at ht
  let outFile := pack B hB (bitList code (trim hpad (unshiftedRecords s r h four)))
  let total := ((n*w+B-1)/B+(s*r*w+B-1)/B)+c1+ex.2+c3+
    (2*((s*r*w+B-1)/B)+2*(((s+1)*r*w+B-1)/B)+c4)+
    ((s*r*w+B-1)/B+(n*w+B-1)/B)
  refine ⟨(outFile,total),?_,rfl,?_⟩
  · dsimp only [s,r] at hex hout hhalf ht
    simp only [runNode,hp,h1,hex,hout,h3,hhalf,ht,bind,Option.bind,pure,
      Prod.fst,Prod.snd,outFile,total,s,r]
  · change ex.2≤charge base cutoff B t w forwardSwaps+c2+charge base cutoff B t w backwardSwaps at hcost
    dsimp only [total,s,r,scanCharge]
    omega

end
end CodedSorting.PhysicalLocalSortNode
end PhysicalLocalSortNode
