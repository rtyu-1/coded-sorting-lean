import CodedSorting.Interchange.Framework.Memory.PaddedChunks
import CodedSorting.Interchange.Framework.Fields.Cost

section Machine
/-! Borrowing and restoring high digits as actual finite-disk instructions.
The scan compiler alternates two files; a charged final copy returns the
result to the source file exactly when the last pass leaves it in scratch.
No initial value is required of RAM or scratch. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonBorrowMachine
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs ScanProgram
open CommonLeafProgram (Machine)
noncomputable section

theorem finalBase_mem {V : ℕ} (ps : List (Pass V)) (source buffer : ℕ) :
    CommonScanProgram.finalBase ps source buffer = source ∨
      CommonScanProgram.finalBase ps source buffer = buffer := by
  induction ps generalizing source buffer with
  | nil => exact Or.inl rfl
  | cons p ps ih => exact (ih buffer source).symm

def code (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source buffer : ℕ) : List (Instruction q) :=
  CommonScanProgram.code q reader ps source buffer ++
    if CommonScanProgram.finalBase ps source buffer = source then []
    else CommonRecursiveExchange.copyCode q reader V buffer source

def charge (q : Configuration) {V : ℕ} (ps : List (Pass V)) : ℕ :=
  (3 * totalConstant ps + 6) * count q V

theorem raw_correct (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source buffer limit : ℕ)
    (hs : source + count q V ≤ buffer)
    (hw : buffer + count q V ≤ limit) (hl : limit ≤ q.N ^ q.exponent)
    (s : Machine q) (y : Fin V) :
    readBit q (executeRaw q (code q reader ps source buffer) s).1.disk source y.val =
      readBit q s.disk source ((destination ps).symm y).val := by
  have hsource : source + count q V ≤ q.N ^ q.exponent := by omega
  have hbuffer : buffer + count q V ≤ q.N ^ q.exponent := by omega
  have hscan := CommonScanProgram.raw_correct q reader ps source buffer s
    hsource hbuffer (Or.inl hs)
  by_cases he : CommonScanProgram.finalBase ps source buffer = source
  · simpa [code, he] using hscan y
  · have hb := (finalBase_mem ps source buffer).resolve_left he
    have hcopy := (CommonRecursiveExchange.copyCode_raw q reader V buffer source
      (executeRaw q (CommonScanProgram.code q reader ps source buffer) s).1
      hbuffer hsource (Or.inr hs)).1 y
    rw [code, if_neg he, raw_append, hcopy]
    simpa only [hb] using hscan y

theorem raw_frame (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source buffer limit : ℕ)
    (hs : source + count q V ≤ buffer)
    (hw : buffer + count q V ≤ limit) (hl : limit ≤ q.N ^ q.exponent)
    (s : Machine q) (a : Fin (q.N ^ q.exponent))
    (ha : a.val < source ∨ source + count q V ≤ a.val)
    (hb : a.val < buffer ∨ limit ≤ a.val) :
    (executeRaw q (code q reader ps source buffer) s).1.disk a = s.disk a := by
  have hsource : source + count q V ≤ q.N ^ q.exponent := by omega
  have hbuffer : buffer + count q V ≤ q.N ^ q.exponent := by omega
  have hscan := CommonScanProgram.raw_outside q reader ps source buffer s
    hsource hbuffer (Or.inl hs) a ha (by omega)
  by_cases he : CommonScanProgram.finalBase ps source buffer = source
  · simpa [code, he] using hscan
  · have hcopy := (CommonRecursiveExchange.copyCode_raw q reader V buffer source
      (executeRaw q (CommonScanProgram.code q reader ps source buffer) s).1
      hbuffer hsource (Or.inr hs)).2 a ha
    rw [code, if_neg he, raw_append, hcopy]
    exact hscan

theorem code_safe (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source buffer : ℕ) :
    ∀ i ∈ code q reader ps source buffer, RespectsPC q i := by
  intro i hi
  rw [code] at hi
  rcases List.mem_append.mp hi with hi | hi
  · exact CommonScanProgram.code_safe q reader ps source buffer i hi
  · split_ifs at hi with he
    · simp at hi
    · exact CommonRecursiveExchange.copyCode_safe q reader V buffer source i hi

theorem code_cost (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source buffer : ℕ) :
    cost q (code q reader ps source buffer) ≤ charge q ps := by
  have hscan := CommonScanProgram.code_cost q reader ps source buffer
  have hcopy := CommonRecursiveExchange.copyCode_cost q reader V buffer source
  rw [code, cost_append]
  unfold charge
  split_ifs <;> (try simp only [cost, List.map_nil, List.sum_nil]) <;> nlinarith

theorem code_length (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source buffer : ℕ) :
    (code q reader ps source buffer).length ≤ charge q ps := by
  have hscan := CommonScanProgram.code_length q reader ps source buffer
  have hcopy := CommonRecursiveExchange.copyCode_length q reader V buffer source
  rw [code, List.length_append]
  unfold charge
  split_ifs <;> (try simp only [List.length_nil]) <;> nlinarith

def program (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source buffer limit : ℕ)
    (hs : source + count q V ≤ buffer)
    (hw : buffer + count q V ≤ limit) (hl : limit ≤ q.N ^ q.exponent) :
    CommonFinitePermutation.Program q V source buffer limit (destination ps).symm where
  instructions := code q reader ps source buffer
  charge := charge q ps
  correct := raw_correct q reader ps source buffer limit hs hw hl
  frame := raw_frame q reader ps source buffer limit hs hw hl
  safe := code_safe q reader ps source buffer
  cost_le := code_cost q reader ps source buffer
  length_le := code_length q reader ps source buffer

@[simp] theorem program_charge (q : Configuration) {V : ℕ}
    (reader : Fin q.inventory.readers) (ps : List (Pass V)) (source buffer limit : ℕ)
    (hs : source + count q V ≤ buffer)
    (hw : buffer + count q V ≤ limit) (hl : limit ≤ q.N ^ q.exponent) :
    (program q reader ps source buffer limit hs hw hl).charge =
      (3 * totalConstant ps + 6) * count q V := rfl

theorem borrow_charge (q : Configuration) (O radix ρ L G S : ℕ) :
    charge q (BorrowScan.borrowProgram O radix ρ L G S) =
      (3 * (ρ * (2 * radix + 6)) + 6) * count q (BorrowScan.volume O (radix ^ ρ) L G S) := by
  rw [charge, BorrowScan.borrowProgram_constant]

theorem finish_charge (q : Configuration) (O radix ρ L G S : ℕ) :
    charge q (BorrowScan.finishProgram O radix ρ L G S) =
      (3 * (ρ * (2 * radix + 6)) + 6) * count q (BorrowScan.volume O (radix ^ ρ) L G S) := by
  rw [charge, BorrowScan.finishProgram_constant]

def borrowProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (O radix ρ L G S source buffer limit : ℕ)
    (hs : source + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ buffer)
    (hw : buffer + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) :
    CommonFinitePermutation.Program q (BorrowScan.volume O (radix ^ ρ) L G S)
      source buffer limit (BorrowScan.borrowPermutation O (radix ^ ρ) L G S).symm :=
  (program q reader (BorrowScan.borrowProgram O radix ρ L G S)
    source buffer limit hs hw hl).changePermutation
      (congrArg Equiv.symm (BorrowScan.borrowProgram_destination O radix ρ L G S))

def finishProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (O radix ρ L G S source buffer limit : ℕ)
    (hs : source + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ buffer)
    (hw : buffer + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) :
    CommonFinitePermutation.Program q (BorrowScan.volume O (radix ^ ρ) L G S)
      source buffer limit (BorrowScan.finishPermutation O (radix ^ ρ) L G S).symm :=
  (program q reader (BorrowScan.finishProgram O radix ρ L G S)
    source buffer limit hs hw hl).changePermutation
      (congrArg Equiv.symm (BorrowScan.finishProgram_destination O radix ρ L G S))

private theorem change_charge (q : Configuration) {V source buffer limit : ℕ}
    {π π' : Equiv.Perm (Fin V)}
    (p : CommonFinitePermutation.Program q V source buffer limit π) (h : π = π') :
    (p.changePermutation h).charge = p.charge := by
  subst π'
  rfl

@[simp] theorem borrowProgram_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (O radix ρ L G S source buffer limit : ℕ)
    (hs : source + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ buffer)
    (hw : buffer + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) :
    (borrowProgram q reader O radix ρ L G S source buffer limit hs hw hl).charge =
      (3 * (ρ * (2 * radix + 6)) + 6) * count q (BorrowScan.volume O (radix ^ ρ) L G S) := by
  rw [borrowProgram, change_charge]
  exact borrow_charge q O radix ρ L G S

@[simp] theorem finishProgram_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (O radix ρ L G S source buffer limit : ℕ)
    (hs : source + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ buffer)
    (hw : buffer + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) :
    (finishProgram q reader O radix ρ L G S source buffer limit hs hw hl).charge =
      (3 * (ρ * (2 * radix + 6)) + 6) * count q (BorrowScan.volume O (radix ^ ρ) L G S) := by
  rw [finishProgram, change_charge]
  exact finish_charge q O radix ρ L G S

/-- The destination is the explicit borrowed address codec, not an assumed
file-level operation. -/
theorem borrow_at (q : Configuration) (reader : Fin q.inventory.readers)
    (O radix ρ L G S source buffer limit : ℕ)
    (hs : source + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ buffer)
    (hw : buffer + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) (s : Machine q)
    (a : BorrowScan.Orig O (radix ^ ρ) L G S) :
    readBit q (executeRaw q
      (borrowProgram q reader O radix ρ L G S source buffer limit hs hw hl).instructions s).1.disk
      source (BorrowScan.borrowedCodec O (radix ^ ρ) L G S (ArbitraryShapes.borrow a)).val =
    readBit q s.disk source (BorrowScan.originalCodec O (radix ^ ρ) L G S a).val := by
  rw [(borrowProgram q reader O radix ρ L G S source buffer limit hs hw hl).correct]
  simp only [BorrowScan.borrowPermutation, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply]
  rfl

theorem finish_at (q : Configuration) (reader : Fin q.inventory.readers)
    (O radix ρ L G S source buffer limit : ℕ)
    (hs : source + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ buffer)
    (hw : buffer + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) (s : Machine q)
    (a : BorrowScan.Borrow O (radix ^ ρ) L G S) :
    readBit q (executeRaw q
      (finishProgram q reader O radix ρ L G S source buffer limit hs hw hl).instructions s).1.disk
      source (BorrowScan.originalCodec O (radix ^ ρ) L G S (ArbitraryShapes.finish a)).val =
    readBit q s.disk source (BorrowScan.borrowedCodec O (radix ^ ρ) L G S a).val := by
  rw [(finishProgram q reader O radix ρ L G S source buffer limit hs hw hl).correct]
  simp only [BorrowScan.finishPermutation, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply]
  rfl

end
end CodedSorting.CommonBorrowMachine
end Machine

section Layout
/-! Literal integer-address composition of borrow, inner field exchange,
and restoration.  This is a pure bridge for the actual finite-machine
programs; it introduces no file interpreter or data-movement hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonBorrowLayout
open Address ArbitraryShapes CoordinateScans BorrowScan PhysicalBorrowLayout
open CommonChunkLayout (Volume swap swap_encoded)
noncomputable section

def originalSwap (O H L G S : ℕ) : Equiv.Perm (Fin (volume O H L G S)) :=
  (finCongr (original_volume O H L G S)).symm.trans
    ((swap O (H*L) G S).trans (finCongr (original_volume O H L G S)))

def borrowedSwap (O H L G S : ℕ) : Equiv.Perm (Fin (volume O H L G S)) :=
  (finCongr (borrowed_volume O H L G S)).symm.trans
    ((swap (O*(H*H)) L G S).trans (finCongr (borrowed_volume O H L G S)))

theorem original_address_val (O H L G S : ℕ) (a : Orig O H L G S) :
    (lowLayout (PhysicalChunkLayout.productShape O H L G S a)).val=
      (originalCodec O H L G S a).val :=
  congrArg Fin.val (original_address O H L G S a)

theorem borrowed_address_val (O H L G S : ℕ) (a : Borrow O H L G S) :
    (lowLayout (borrowedShape O H L G S a)).val=(borrowedCodec O H L G S a).val :=
  congrArg Fin.val (borrowed_address O H L G S a)

theorem borrowed_shape_exchange (O H L G S : ℕ) (a : Borrow O H L G S) :
    exchange (borrowedShape O H L G S a)=borrowedShape O H L G S (exchange a) := rfl

theorem originalSwap_encoded (O H L G S : ℕ) (a : Orig O H L G S) :
    originalSwap O H L G S (originalCodec O H L G S a)=
      originalCodec O H L G S (exchange a) := by
  rw [←original_address O H L G S a]
  simp only [originalSwap,Equiv.trans_apply,Equiv.symm_apply_apply,swap_encoded]
  exact original_address O H L G S (exchange a)

theorem borrowedSwap_encoded (O H L G S : ℕ) (a : Borrow O H L G S) :
    borrowedSwap O H L G S (borrowedCodec O H L G S a)=
      borrowedCodec O H L G S (exchange a) := by
  rw [←borrowed_address O H L G S a]
  simp only [borrowedSwap,Equiv.trans_apply,Equiv.symm_apply_apply,swap_encoded,
    borrowed_shape_exchange]
  exact borrowed_address O H L G S (exchange a)

theorem borrow_inverse_encoded (O H L G S : ℕ) (a : Borrow O H L G S) :
    (borrowPermutation O H L G S).symm (borrowedCodec O H L G S a)=
      originalCodec O H L G S (borrowEquiv.symm a) := by
  simp only [borrowPermutation,Equiv.symm_trans_apply,Equiv.symm_symm,
    Equiv.symm_apply_apply]

theorem finish_inverse_encoded (O H L G S : ℕ) (a : Orig O H L G S) :
    (finishPermutation O H L G S).symm (originalCodec O H L G S a)=
      borrowedCodec O H L G S (finishEquiv.symm a) := by
  simp only [finishPermutation,Equiv.symm_trans_apply,Equiv.symm_symm,
    Equiv.symm_apply_apply]

theorem inverse_borrow_exchange_finish (O H L G S : ℕ) (a : Orig O H L G S) :
    borrowEquiv.symm (exchange (finishEquiv.symm a))=exchange a := by
  cases a
  rfl

/-- Pullbacks compose in reverse execution order: finish, inner exchange,
then borrow. Their result is exactly the original full-field swap. -/
theorem composition (O H L G S : ℕ) :
    (finishPermutation O H L G S).symm.trans
      ((borrowedSwap O H L G S).trans (borrowPermutation O H L G S).symm)=
        originalSwap O H L G S := by
  apply Equiv.ext
  intro i
  obtain ⟨a,rfl⟩ := (originalCodec O H L G S).surjective i
  simp only [Equiv.trans_apply,finish_inverse_encoded,borrowedSwap_encoded,
    borrow_inverse_encoded,inverse_borrow_exchange_finish,originalSwap_encoded]

theorem originalSwap_cast (O H L G S : ℕ) (i : Fin (Volume O (H*L) G S)) :
    originalSwap O H L G S (finCongr (original_volume O H L G S) i)=
      finCongr (original_volume O H L G S) (swap O (H*L) G S i) := by
  simp only [originalSwap,Equiv.trans_apply,Equiv.symm_apply_apply]

theorem borrowedSwap_cast (O H L G S : ℕ) (i : Fin (Volume (O*(H*H)) L G S)) :
    borrowedSwap O H L G S (finCongr (borrowed_volume O H L G S) i)=
      finCongr (borrowed_volume O H L G S) (swap (O*(H*H)) L G S i) := by
  simp only [borrowedSwap,Equiv.trans_apply,Equiv.symm_apply_apply]

/-- Natural addresses erase all volume casts. The three hypotheses can
therefore be filled directly by the three actual machine fragments. -/
theorem borrow_finish_correct {Value : Type*} (O H L G S : ℕ)
    (input middle changed output : ℕ→Value)
    (hb : ∀ i : Fin (volume O H L G S),
      middle i.val=input ((borrowPermutation O H L G S).symm i).val)
    (hx : ∀ i : Fin (Volume (O*(H*H)) L G S),
      changed i.val=middle (swap (O*(H*H)) L G S i).val)
    (hf : ∀ i : Fin (volume O H L G S),
      output i.val=changed ((finishPermutation O H L G S).symm i).val) :
    ∀ i : Fin (Volume O (H*L) G S),
      output i.val=input (swap O (H*L) G S i).val := by
  intro i
  let j := finCongr (original_volume O H L G S) i
  have hfinish := hf j
  let u := (finishPermutation O H L G S).symm j
  let v := (finCongr (borrowed_volume O H L G S)).symm u
  have hinner := hx v
  have hcast : (swap (O*(H*H)) L G S v).val=(borrowedSwap O H L G S u).val := by
    have hh := borrowedSwap_cast O H L G S v
    simpa only [v,Equiv.apply_symm_apply,finCongr_apply_coe] using (congrArg Fin.val hh).symm
  rw [hcast] at hinner
  have hborrow := hb (borrowedSwap O H L G S u)
  have hcomp := congrArg (fun p : Equiv.Perm (Fin (volume O H L G S)) => p j)
    (composition O H L G S)
  simp only [Equiv.trans_apply] at hcomp
  have hout : output j.val=input (originalSwap O H L G S j).val := by
    calc
      output j.val=changed u.val := hfinish
      _=middle (borrowedSwap O H L G S u).val := hinner
      _=input ((borrowPermutation O H L G S).symm (borrowedSwap O H L G S u)).val := hborrow
      _=input (originalSwap O H L G S j).val := congrArg (fun x => input x.val) hcomp
  simpa only [j,originalSwap_cast,finCongr_apply_coe] using hout

end
end CodedSorting.CommonBorrowLayout
end Layout

section Core
/-! Composition of actual borrowing, a proved inner exchange program, and
actual restoration. The three phases pass the same finite machine state.
The inner program may use arbitrary scratch values left by borrowing. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonBorrowedCore
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonFinitePermutation CommonChunkLayout
noncomputable section

def liftedInner (q : Configuration) (O H L G S source buffer limit : ℕ)
    (p : Program q (Volume (O * (H * H)) L G S) source buffer limit
      (swap (O * (H * H)) L G S)) :
    Program q (BorrowScan.volume O H L G S) source buffer limit
      (CommonBorrowLayout.borrowedSwap O H L G S) :=
  p.castVolume (PhysicalBorrowLayout.borrowed_volume O H L G S)

def composed (q : Configuration) (reader : Fin q.inventory.readers)
    (O radix ρ L G S source buffer limit : ℕ)
    (p : Program q (Volume (O * ((radix ^ ρ) * (radix ^ ρ))) L G S)
      source buffer limit (swap (O * ((radix ^ ρ) * (radix ^ ρ))) L G S))
    (hs : source + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ buffer)
    (hw : buffer + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) :
    Program q (BorrowScan.volume O (radix ^ ρ) L G S) source buffer limit
      ((BorrowScan.finishPermutation O (radix ^ ρ) L G S).symm.trans
        ((CommonBorrowLayout.borrowedSwap O (radix ^ ρ) L G S).trans
          (BorrowScan.borrowPermutation O (radix ^ ρ) L G S).symm)) :=
  ((CommonBorrowMachine.borrowProgram q reader O radix ρ L G S source buffer limit hs hw hl).append
    (liftedInner q O (radix ^ ρ) L G S source buffer limit p)).append
      (CommonBorrowMachine.finishProgram q reader O radix ρ L G S source buffer limit hs hw hl)

def exchanged (q : Configuration) (reader : Fin q.inventory.readers)
    (O radix ρ L G S source buffer limit : ℕ)
    (p : Program q (Volume (O * ((radix ^ ρ) * (radix ^ ρ))) L G S)
      source buffer limit (swap (O * ((radix ^ ρ) * (radix ^ ρ))) L G S))
    (hs : source + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ buffer)
    (hw : buffer + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) :
    Program q (BorrowScan.volume O (radix ^ ρ) L G S) source buffer limit
      (CommonBorrowLayout.originalSwap O (radix ^ ρ) L G S) :=
  (composed q reader O radix ρ L G S source buffer limit p hs hw hl).changePermutation
    (CommonBorrowLayout.composition O (radix ^ ρ) L G S)

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (O radix ρ L G S source buffer limit : ℕ)
    (p : Program q (Volume (O * ((radix ^ ρ) * (radix ^ ρ))) L G S)
      source buffer limit (swap (O * ((radix ^ ρ) * (radix ^ ρ))) L G S))
    (hs : source + count q (Volume O ((radix ^ ρ) * L) G S) ≤ buffer)
    (hw : buffer + count q (Volume O ((radix ^ ρ) * L) G S) ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) :
    Program q (Volume O ((radix ^ ρ) * L) G S) source buffer limit
      (swap O ((radix ^ ρ) * L) G S) := by
  let hv := PhysicalBorrowLayout.original_volume O (radix ^ ρ) L G S
  let t := exchanged q reader O radix ρ L G S source buffer limit p
    (by simpa only [← hv] using hs) (by simpa only [← hv] using hw) hl
  refine {
    instructions := t.instructions
    charge := t.charge
    correct := ?_
    frame := ?_
    safe := t.safe
    cost_le := t.cost_le
    length_le := t.length_le }
  · intro s y
    have h := t.correct s (finCongr hv y)
    simpa only [CommonBorrowLayout.originalSwap_cast, finCongr_apply_coe] using h
  · intro s a ha hb
    exact t.frame s a (by simpa only [← hv] using ha) hb

private theorem change_charge (q : Configuration) {V source buffer limit : ℕ}
    {π π' : Equiv.Perm (Fin V)} (p : Program q V source buffer limit π) (h : π = π') :
    (p.changePermutation h).charge = p.charge := by
  subst π'
  rfl

theorem exchanged_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (O radix ρ L G S source buffer limit : ℕ)
    (p : Program q (Volume (O * ((radix ^ ρ) * (radix ^ ρ))) L G S)
      source buffer limit (swap (O * ((radix ^ ρ) * (radix ^ ρ))) L G S))
    (hs : source + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ buffer)
    (hw : buffer + count q (BorrowScan.volume O (radix ^ ρ) L G S) ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) :
    (exchanged q reader O radix ρ L G S source buffer limit p hs hw hl).charge =
      p.charge + 2 * ((3 * (ρ * (2 * radix + 6)) + 6) *
        count q (BorrowScan.volume O (radix ^ ρ) L G S)) := by
  rw [exchanged, change_charge]
  change (CommonBorrowMachine.borrowProgram q reader O radix ρ L G S
    source buffer limit hs hw hl).charge + p.charge +
    (CommonBorrowMachine.finishProgram q reader O radix ρ L G S
      source buffer limit hs hw hl).charge = _
  rw [CommonBorrowMachine.borrowProgram_charge, CommonBorrowMachine.finishProgram_charge]
  ring

@[simp] theorem program_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (O radix ρ L G S source buffer limit : ℕ)
    (p : Program q (Volume (O * ((radix ^ ρ) * (radix ^ ρ))) L G S)
      source buffer limit (swap (O * ((radix ^ ρ) * (radix ^ ρ))) L G S))
    (hs : source + count q (Volume O ((radix ^ ρ) * L) G S) ≤ buffer)
    (hw : buffer + count q (Volume O ((radix ^ ρ) * L) G S) ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) :
    (program q reader O radix ρ L G S source buffer limit p hs hw hl).charge =
      p.charge + 2 * ((3 * (ρ * (2 * radix + 6)) + 6) *
        count q (Volume O ((radix ^ ρ) * L) G S)) := by
  dsimp only [program]
  rw [exchanged_charge, ← PhysicalBorrowLayout.original_volume]

end
end CodedSorting.CommonBorrowedCore
end Core

section Chunks
/-! The actual high-digit path: borrow, pad the resulting prefix, execute
all unequal-width chunks, remove padding, and restore the high digits.
Every phase consumes the actual preceding machine state, and every transfer
is included in the final charge. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonBorrowedChunks
open CommonSortingNormalization CommonPermutationPairs CommonFinitePermutation
open CommonChunkLayout PhysicalChunkExchange CommonChunkExchange RecursiveExchange Circuit
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m

theorem borrowed_volume (O H L G S : ℕ) :
    Volume O (H * L) G S = Volume (O * (H * H)) L G S :=
  (PhysicalBorrowLayout.original_volume O H L G S).trans
    (PhysicalBorrowLayout.borrowed_volume O H L G S).symm

/-- All phases reuse one scratch interval. The sum is a public sufficient
allocation for the borrow file and the padded chunk program. -/
def space (q : Configuration) (cutoff : ℕ) (cs : List ArbitraryRecursive.Call)
    (O ρ P' G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (hc : Conditions q cutoff cs P') : ℕ :=
  count q (Volume O ((RecursiveExchange.radix ^ ρ) * fieldCount cs) G (S * q.w)) +
    CommonPaddedChunks.space q cutoff cs P' G S hG hS hc

def bound (q : Configuration) (cutoff : ℕ) (cs : List ArbitraryRecursive.Call) (O ρ P' G S : ℕ) : ℕ :=
  CommonChunkCost.totalBound cutoff (width q) cs
    (Volume P' (fieldCount cs) G (S * q.w)) +
  (24 + 6 * ρ * (2 * RecursiveExchange.radix + 6)) *
    count q (Volume O ((RecursiveExchange.radix ^ ρ) * fieldCount cs) G (S * q.w)) +
  27 * count q (Volume P' (fieldCount cs) G (S * q.w))

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) (cs : List ArbitraryRecursive.Call) (O ρ P' G S source buffer limit : ℕ)
    (hG : 0 < G) (hS : 0 < S)
    (hp : O * ((RecursiveExchange.radix ^ ρ) * (RecursiveExchange.radix ^ ρ)) ≤ P')
    (hc : Conditions q cutoff cs P')
    (hs : source + count q
      (Volume O ((RecursiveExchange.radix ^ ρ) * fieldCount cs) G (S * q.w)) ≤ buffer)
    (hw : buffer + space q cutoff cs O ρ P' G S hG hS hc ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) :
    Program q (Volume O ((RecursiveExchange.radix ^ ρ) * fieldCount cs) G (S * q.w))
      source buffer limit (swap O ((RecursiveExchange.radix ^ ρ) * fieldCount cs) G (S * q.w)) := by
  let H := RecursiveExchange.radix ^ ρ
  have hsinner : source + count q (Volume (O * (H * H)) (fieldCount cs) G (S * q.w)) ≤ buffer := by
    simpa only [← borrowed_volume] using hs
  have hwpadded : buffer + CommonPaddedChunks.space q cutoff cs P' G S hG hS hc ≤ limit := by
    dsimp only [space] at hw
    omega
  have hwborrow : buffer + count q (Volume O (H * fieldCount cs) G (S * q.w)) ≤ limit := by
    dsimp only [H]
    dsimp only [space] at hw
    omega
  let p := CommonPaddedChunks.program q reader cutoff cs (O * (H * H)) P' G S
    source buffer limit hG hS hp hc hsinner hwpadded hl
  exact CommonBorrowedCore.program q reader O RecursiveExchange.radix ρ
    (fieldCount cs) G (S * q.w) source buffer limit p hs hwborrow hl

@[simp] theorem program_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) (cs : List ArbitraryRecursive.Call) (O ρ P' G S source buffer limit : ℕ)
    (hG : 0 < G) (hS : 0 < S)
    (hp : O * ((RecursiveExchange.radix ^ ρ) * (RecursiveExchange.radix ^ ρ)) ≤ P')
    (hc : Conditions q cutoff cs P')
    (hs : source + count q
      (Volume O ((RecursiveExchange.radix ^ ρ) * fieldCount cs) G (S * q.w)) ≤ buffer)
    (hw : buffer + space q cutoff cs O ρ P' G S hG hS hc ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) :
    (program q reader cutoff cs O ρ P' G S source buffer limit hG hS hp hc hs hw hl).charge =
      bound q cutoff cs O ρ P' G S := by
  simp only [program, CommonBorrowedCore.program_charge, CommonPaddedChunks.program_charge,
    CommonPaddedChunks.bound, bound, ← borrowed_volume]
  ring

/-- The actual transfer charge fits the arithmetic envelope used in the
arbitrary-width theorem, including both borrowing scans and both padding scans. -/
theorem bound_le_scan (q : Configuration) (cutoff : ℕ) (cs : List ArbitraryRecursive.Call)
    (O ρ P' G S : ℕ) :
    bound q cutoff cs O ρ P' G S ≤
      CommonArbitraryCost.borrowedBound cutoff (width q) cs O ρ P' G (S * q.w)
        24 27 (6 * (2 * RecursiveExchange.radix + 6)) := by
  let V := Volume O ((RecursiveExchange.radix ^ ρ) * fieldCount cs) G (S * q.w)
  let V' := Volume P' (fieldCount cs) G (S * q.w)
  have h := CommonArbitraryCost.assembled_overhead_le q cutoff V V' ρ cs
  have he : bound q cutoff cs O ρ P' G S =
      CommonChunkCost.totalBound cutoff (width q) cs V' +
        2 * ((3 * ρ * (2 * RecursiveExchange.radix + 6) + 6) * count q V) +
        (12 * count q V + 27 * count q V') := by
    unfold bound V V'
    ring
  rw [he, CommonArbitraryCost.borrowedBound, ← PhysicalBorrowLayout.original_volume]
  exact h

end
end CodedSorting.CommonBorrowedChunks
end Chunks
