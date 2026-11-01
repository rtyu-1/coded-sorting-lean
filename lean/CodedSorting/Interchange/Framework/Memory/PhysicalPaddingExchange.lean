import CodedSorting.Shared.Memory.PhysicalRecursionBound
import CodedSorting.Interchange.Framework.Recursion.ArbitraryRecursive

section BorrowScan
/-! Actual digit-scan implementations of Appendix C's borrow/finish maps,
under explicit row-major codecs. Reassociation is proved by numeric position
formulas rather than supplied as a data-moving operation. -/

namespace CodedSorting.BorrowScan
open Address ArbitraryShapes BlockDigitMove ScanProgram TriangularStreams

abbrev Orig (O H L G S : ℕ) :=
  Original (Prefix := Fin O) (High := Fin H) (Low := Fin L) (Gap := Fin G) (Suffix := Fin S)
abbrev Borrow (O H L G S : ℕ) :=
  Borrowed (Prefix := Fin O) (High := Fin H) (Low := Fin L) (Gap := Fin G) (Suffix := Fin S)

def volume (O H L G S : ℕ) := O*((H*(L*G))*(H*(L*S)))

/-- Only regroup consecutive fields; the first high field, low field and
gap form the contiguous field preceding D's high field. -/
def originalGroup (O H L G S : ℕ) : Orig O H L G S ≃
    (Fin O × TripleAddress (H*(L*G)) H (L*S)) where
  toFun a := (a.prefixCoord,tripleEncode (a.high.1,a.high.2,a.gap),
    a.low.1,finProdFinEquiv (a.low.2,a.suffix))
  invFun x :=
    let hlg := tripleEncode.symm x.2.1
    let ls := finProdFinEquiv.symm x.2.2.2
    ⟨x.1,(hlg.1,hlg.2.1),hlg.2.2,(x.2.2.1,ls.1),ls.2⟩
  left_inv a := by cases a; simp
  right_inv x := by
    rcases x with ⟨o,p,h,s⟩
    simp
    exact finProdFinEquiv.apply_symm_apply s

/-- The borrowed prefix is (original prefix, D-high, H-high). -/
def borrowedGroup (O H L G S : ℕ) : Borrow O H L G S ≃
    (Fin O × TripleAddress H (H*(L*G)) (L*S)) where
  toFun a := (a.prefixCoord.1,a.prefixCoord.2.1,
    tripleEncode (a.prefixCoord.2.2,a.high,a.gap),finProdFinEquiv (a.low,a.suffix))
  invFun x :=
    let hlg := tripleEncode.symm x.2.2.1
    let ls := finProdFinEquiv.symm x.2.2.2
    ⟨(x.1,x.2.1,hlg.1),hlg.2.1,hlg.2.2,ls.1,ls.2⟩
  left_inv a := by cases a; simp
  right_inv x := by
    rcases x with ⟨o,h,p,s⟩
    simp
    exact finProdFinEquiv.apply_symm_apply s

def fourCodec (O P H S : ℕ) : (Fin O × TripleAddress P H S) ≃ Fin (O*(P*(H*S))) :=
  (Equiv.prodCongr (Equiv.refl _) tripleEncode).trans finProdFinEquiv

def originalCodec (O H L G S : ℕ) : Orig O H L G S ≃ Fin (volume O H L G S) :=
  (originalGroup O H L G S).trans (fourCodec O (H*(L*G)) H (L*S))

def borrowedCodec (O H L G S : ℕ) : Borrow O H L G S ≃ Fin (volume O H L G S) :=
  (borrowedGroup O H L G S).trans
    ((fourCodec O H (H*(L*G)) (L*S)).trans (finCongr (by unfold volume; ring)))

theorem originalCodec_val (O H L G S : ℕ) (a : Orig O H L G S) :
    (originalCodec O H L G S a).val =
      a.prefixCoord.val*((H*(L*G))*(H*(L*S))) +
      (tripleEncode (a.high.1,a.high.2,a.gap)).val*(H*(L*S))+
      a.low.1.val*(L*S)+(finProdFinEquiv (a.low.2,a.suffix)).val := by
  change (encode O (H*(L*G)) H (L*S) a.prefixCoord
    (tripleEncode (a.high.1,a.high.2,a.gap)) a.low.1
    (finProdFinEquiv (a.low.2,a.suffix))).val = _
  rw [encode_val]



def borrowProgram (O q ρ L G S : ℕ) : List (Pass (volume O (q^ρ) L G S)) :=
  program O ((q^ρ)*(L*G)) q (L*S) ρ

def finishProgram (O q ρ L G S : ℕ) : List (Pass (volume O (q^ρ) L G S)) :=
  castProgram (by unfold volume; ring)
    (inverseProgram (program (O*(q^ρ)) (L*G) q (L*S) ρ))

/-- Each payload reaches exactly the address specified by `borrow`. -/
theorem borrow_destination (O q ρ L G S : ℕ) (a : Orig O (q^ρ) L G S) :
    destination (borrowProgram O q ρ L G S) (originalCodec O (q^ρ) L G S a) =
      borrowedCodec O (q^ρ) L G S (borrow a) := by
  apply Fin.ext
  change (destination (program O ((q^ρ)*(L*G)) q (L*S) ρ)
    (encode O ((q^ρ)*(L*G)) (q^ρ) (L*S) a.prefixCoord
      (tripleEncode (a.high.1,a.high.2,a.gap)) a.low.1
      (finProdFinEquiv (a.low.2,a.suffix)))).val = _
  rw [program_encoded]
  simp [borrowedCodec,borrowedGroup,borrow,fourCodec,volume,tripleEncode,
    finCongr,finProdFinEquiv] <;> ring


/-- Restoring the high fields is the inverse block move inside the prefix
that already contains D-high. It implements `finish`, not `unborrow`. -/
theorem finish_destination (O q ρ L G S : ℕ) (a : Borrow O (q^ρ) L G S) :
    destination (finishProgram O q ρ L G S) (borrowedCodec O (q^ρ) L G S a) =
      originalCodec O (q^ρ) L G S (finish a) := by
  let hsize : (O*(q^ρ))*((L*G)*((q^ρ)*(L*S)))=volume O (q^ρ) L G S := by
    unfold volume
    ring
  let x := encode (O*(q^ρ)) (L*G) (q^ρ) (L*S)
    (finProdFinEquiv (a.prefixCoord.1,a.prefixCoord.2.1))
    (finProdFinEquiv (a.high,a.gap)) a.prefixCoord.2.2
    (finProdFinEquiv (a.low,a.suffix))
  have hin : finCongr hsize x=originalCodec O (q^ρ) L G S (finish a) := by
    apply Fin.ext
    change x.val=(originalCodec O (q^ρ) L G S (finish a)).val
    rw [originalCodec_val]
    simp [x,encode_val,finish,tripleEncode,finProdFinEquiv] <;> ring
  have hout : finCongr hsize (destination (program (O*(q^ρ)) (L*G) q (L*S) ρ) x)=
      borrowedCodec O (q^ρ) L G S a := by
    apply Fin.ext
    change (destination (program (O*(q^ρ)) (L*G) q (L*S) ρ) x).val = _
    rw [program_encoded]
    simp [borrowedCodec,borrowedGroup,fourCodec,volume,tripleEncode,
      finCongr,finProdFinEquiv] <;> ring
  change destination (castProgram hsize (inverseProgram (program (O*(q^ρ)) (L*G) q (L*S) ρ))) _ = _
  rw [←hout,castProgram_destination,inverseProgram_destination,Equiv.symm_apply_apply,hin]

def borrowPermutation (O H L G S : ℕ) : Equiv.Perm (Fin (volume O H L G S)) :=
  (originalCodec O H L G S).symm.trans (borrowEquiv.trans (borrowedCodec O H L G S))

def finishPermutation (O H L G S : ℕ) : Equiv.Perm (Fin (volume O H L G S)) :=
  (borrowedCodec O H L G S).symm.trans (finishEquiv.trans (originalCodec O H L G S))

theorem borrowProgram_destination (O q ρ L G S : ℕ) :
    destination (borrowProgram O q ρ L G S)=borrowPermutation O (q^ρ) L G S := by
  apply Equiv.ext
  intro x
  obtain ⟨a,rfl⟩ := (originalCodec O (q^ρ) L G S).surjective x
  simpa [borrowPermutation] using borrow_destination O q ρ L G S a

theorem finishProgram_destination (O q ρ L G S : ℕ) :
    destination (finishProgram O q ρ L G S)=finishPermutation O (q^ρ) L G S := by
  apply Equiv.ext
  intro x
  obtain ⟨a,rfl⟩ := (borrowedCodec O (q^ρ) L G S).surjective x
  simpa [finishPermutation] using finish_destination O q ρ L G S a

theorem borrowProgram_constant (O q ρ L G S : ℕ) :
    totalConstant (borrowProgram O q ρ L G S)=ρ*(2*q+6) :=
  program_constant O ((q^ρ)*(L*G)) q (L*S) ρ

theorem finishProgram_constant (O q ρ L G S : ℕ) :
    totalConstant (finishProgram O q ρ L G S)=ρ*(2*q+6) := by
  rw [finishProgram,castProgram_constant,inverseProgram_constant,program_constant]

theorem borrow_execution {Value : Type*} [Inhabited Value]
    (O q ρ L G S B : ℕ) (hB : 0 < B) (F : Fin (volume O (q^ρ) L G S) → Value) :
    ∃ cost, Execution B hB (borrowProgram O q ρ L G S) F cost ∧
      eval (borrowProgram O q ρ L G S) F=transport (borrowPermutation O (q^ρ) L G S) F ∧
      cost≤ρ*(2*q+6)*(volume O (q^ρ) L G S/B+1) := by
  obtain ⟨cost,he,hc⟩ := program_correct (borrowProgram O q ρ L G S) F B hB
  refine ⟨cost,he,?_,?_⟩
  · funext y
    rw [eval_eq_pullback,borrowProgram_destination]
    rfl
  · simpa only [borrowProgram_constant] using hc

theorem finish_execution {Value : Type*} [Inhabited Value]
    (O q ρ L G S B : ℕ) (hB : 0 < B) (F : Fin (volume O (q^ρ) L G S) → Value) :
    ∃ cost, Execution B hB (finishProgram O q ρ L G S) F cost ∧
      eval (finishProgram O q ρ L G S) F=transport (finishPermutation O (q^ρ) L G S) F ∧
      cost≤ρ*(2*q+6)*(volume O (q^ρ) L G S/B+1) := by
  obtain ⟨cost,he,hc⟩ := program_correct (finishProgram O q ρ L G S) F B hB
  refine ⟨cost,he,?_,?_⟩
  · funext y
    rw [eval_eq_pullback,finishProgram_destination]
    rfl
  · simpa only [finishProgram_constant] using hc



theorem borrowProgram_buffers (O q ρ L G S : ℕ) :
    ∀ p∈borrowProgram O q ρ L G S,p.buffers=q+2 :=
  program_buffers O ((q^ρ)*(L*G)) q (L*S) ρ

theorem finishProgram_buffers (O q ρ L G S : ℕ) :
    ∀ p∈finishProgram O q ρ L G S,p.buffers=q+2 :=
  castProgram_buffers _ _ (inverseProgram_buffers _
    (program_buffers (O*(q^ρ)) (L*G) q (L*S) ρ))

theorem borrowProgram_length (O q ρ L G S : ℕ) :
    (borrowProgram O q ρ L G S).length=ρ :=
  program_length O ((q^ρ)*(L*G)) q (L*S) ρ

theorem finishProgram_length (O q ρ L G S : ℕ) :
    (finishProgram O q ρ L G S).length=ρ := by
  simp [finishProgram,castProgram_length,inverseProgram,program_length]


end CodedSorting.BorrowScan
end BorrowScan

section NormalizedPhysicalExchange
/-! Apply the recursive file interpreter using the base width and memory cutoff chosen from the machine parameters. One fixed block-size ratio establishes the base-case startup and recursive child-size conditions. 



-/
set_option autoImplicit false
namespace CodedSorting.NormalizedPhysicalExchange
open Circuit Address RecursiveExchange PhysicalRecursiveExchange PhysicalFieldPacking
open PhysicalExchangeRecursion PhysicalLeafParameters
noncomputable section

def chosenBase (M B : ℕ) : ℕ := baseWidth Parameters.m radix (M/B)

def cutoff (reserve M w : ℕ) : ℕ := (M/reserve)*w

theorem chosenBase_bounds (reserve M B : ℕ)
    (hnormal : minimumRatio radix reserve Parameters.W ≤ M/B) :
    0 < chosenBase M B ∧ chosenBase M B ≤ widthLimit radix (M/B) ∧
      widthLimit radix (M/B) < Parameters.m * chosenBase M B := by
  exact baseWidth_bounds Parameters.m radix reserve Parameters.W (M/B)
    (by norm_num [Parameters.m_value]) radix_prime.one_lt hnormal

theorem chosenBase_log (reserve M B : ℕ)
    (hnormal : minimumRatio radix reserve Parameters.W ≤ M/B) :
    8*chosenBase M B ≤ Nat.log radix (M/B) ∧
      Nat.log radix (M/B) < 8*Parameters.m*chosenBase M B := by
  exact baseWidth_log_sandwich Parameters.m radix reserve Parameters.W (M/B)
    (by norm_num [Parameters.m_value]) radix_prime.one_lt hnormal

theorem chosenBase_startup (reserve M B w : ℕ) (hreserve : 0 < reserve)
    (hnormal : minimumRatio radix reserve Parameters.W ≤ M/B) :
    (radix^(chosenBase M B)*radix^(chosenBase M B))*(B*w) ≤ cutoff reserve M w := by
  exact bucket_bits radix reserve Parameters.W M B w (chosenBase M B)
    radix_prime.one_lt hreserve hnormal (chosenBase_bounds reserve M B hnormal).2.1

theorem cutoff_child_blocks (reserve M B w : ℕ) (hreserve : 0 < reserve)
    (hnormal : minimumRatio radix reserve Parameters.W ≤ M/B) :
    Parameters.W*(B*w) ≤ cutoff reserve M w := by
  simpa only [cutoff,Nat.mul_assoc] using Nat.mul_le_mul_right w
    (reserved_child_words radix reserve Parameters.W M B hreserve hnormal)

/-- Every canonical input file is processed by this one recursive function.
No child-correctness or child-cost oracle remains in the hypotheses. -/
theorem normalized_run (reserve M B w k rows G S : ℕ) (hreserve : 0 < reserve)
    (hB : 0 < B) (hw : 0 < w) (hG : 0 < G) (hS : 0 < S)
    (hnormal : minimumRatio radix reserve Parameters.W ≤ M/B)
    (F : ScalarData (chosenBase M B*Parameters.m^k) (rows*Parameters.W^k) G S)
    (source : File)
    (hs : source = represented
      (scalarLayout (chosenBase M B*Parameters.m^k) (rows*Parameters.W^k) G S)
      (B*w) (Nat.mul_pos hB hw) F) :
    ∃ result,
      run (chosenBase M B) (cutoff reserve M w) (B*w) (Nat.mul_pos hB hw)
        k rows G S source = some result ∧
      result.1 = represented
        (scalarLayout (chosenBase M B*Parameters.m^k) (rows*Parameters.W^k) G S)
        (B*w) (Nat.mul_pos hB hw) (transport exchangeEquiv F) ∧
      result.2 ≤ costBound (B*w) (cutoff reserve M w) k
        (volume (chosenBase M B) k rows G S) := by
  apply run_correct_cost (chosenBase M B) (cutoff reserve M w) (B*w)
    (Nat.mul_pos hB hw) _ k rows G S hG hS F source hs
  exact (chosenBase_startup reserve M B w hreserve hnormal).trans (Nat.le_add_right _ _)

/-- The improved bound applies to the same file execution after deriving the startup and cutoff conditions from M, B, and w. 
-/
theorem normalized_exchange_bound (reserve M B w k rows G S : ℕ) (hreserve : 0 < reserve)
    (hB : 0 < B) (hw : 0 < w) (hG : 0 < G) (hS : 0 < S)
    (hnormal : minimumRatio radix reserve Parameters.W ≤ M/B)
    (F : ScalarData (chosenBase M B*Parameters.m^k) (rows*Parameters.W^k) G S)
    (source : File)
    (hs : source = represented
      (scalarLayout (chosenBase M B*Parameters.m^k) (rows*Parameters.W^k) G S)
      (B*w) (Nat.mul_pos hB hw) F) :
    ∃ result,
      run (chosenBase M B) (cutoff reserve M w) (B*w) (Nat.mul_pos hB hw)
        k rows G S source = some result ∧
      result.1 = represented
        (scalarLayout (chosenBase M B*Parameters.m^k) (rows*Parameters.W^k) G S)
        (B*w) (Nat.mul_pos hB hw) (transport exchangeEquiv F) ∧
      (result.2 : ℝ) ≤ PhysicalRecursionBound.boundConstant *
        (1+(volume (chosenBase M B) k rows G S : ℝ)/((B*w : ℕ) : ℝ)*
          (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) := by
  exact PhysicalRecursionBound.actual_recursive_exchange_bound
    (chosenBase M B) (cutoff reserve M w) (B*w) (Nat.mul_pos hB hw)
    ((chosenBase_startup reserve M B w hreserve hnormal).trans (Nat.le_add_right _ _))
    (cutoff_child_blocks reserve M B w hreserve hnormal) k rows G S hG hS F source hs

end
end CodedSorting.NormalizedPhysicalExchange
end NormalizedPhysicalExchange

section PhysicalPaddingExchange
/-! Actual insertion, recursive exchange, and erasure of a padded file.
The recursive routine consumes the returned insertion file; the erasure
consumes that routine's returned output. Costs describe this same run.
This module does not assert a finite-RAM compilation of host recursion. -/

set_option autoImplicit false
set_option maxRecDepth 4096
namespace CodedSorting.PhysicalPaddingExchange
open Circuit Address RecursiveExchange PhysicalRecursiveExchange PhysicalFieldPacking
open PhysicalExchangeRecursion BinaryPadding CoordinateScans BucketMachine BucketReader
noncomputable section

def exchanged {P Q G S : ℕ} (F : Fin (Volume P Q G S) → Bit) :
    Fin (Volume P Q G S) → Bit :=
  fun y => F (lowLayout (exchange (lowLayout.symm y : Addr P Q G S)))

def insertFile (P n m G S B : ℕ) (source : File) : Option Result :=
  (StreamMask.insert
    (BinaryPaddingScan.maskNat (BinaryPaddingScan.keep (P:=P) (m:=m) (G:=G) (S:=S) n))
    (0 : Bit) B (Volume P m G S) 0 ⟨Reader.fromDisk source,Writer.empty⟩).map
      (fun out => (out.target.finish,out.source.reads+out.target.finish.length))

def eraseFile (P n m G S B : ℕ) (source : File) : Option Result :=
  (StreamMask.erase
    (BinaryPaddingScan.maskNat (BinaryPaddingScan.keep (P:=P) (m:=m) (G:=G) (S:=S) n))
    B (Volume P m G S) 0 ⟨Reader.fromDisk source,Writer.empty⟩).map
      (fun out => (out.target.finish,out.source.reads+out.target.finish.length))

theorem canonical_length {V : ℕ} (B : ℕ) (hB : 0 < B) (F : Fin V → Bit) :
    (canonical B hB F).length = (V+B-1)/B := by
  simp only [canonical,pack_count,List.length_ofFn]

theorem insert_correct (P n m G S B : ℕ) (hB : 0 < B) (h : n ≤ m)
    (F : Fin (Volume P n G S) → Bit) :
    insertFile P n m G S B (canonical B hB F) =
      some (canonical B hB (BinaryPaddingScan.expanded h 0 F),
        (Volume P n G S+B-1)/B+(Volume P m G S+B-1)/B) := by
  obtain ⟨out,hr,ho,hc,_,_⟩ := BinaryPaddingScan.insert_physical h (0 : Bit) B hB F
    (canonical B hB F) (StreamCopy.pack_reader_valid B hB _)
    (by simp only [canonical,flatten_pack,List.ofFn_eq_map])
  simp only [insertFile,hr,Option.map_some]
  apply congrArg some
  apply Prod.ext
  · simpa only [canonical,List.ofFn_eq_map] using ho
  · simpa only [canonical_length] using hc

theorem erase_correct (P n m G S B : ℕ) (hB : 0 < B) (h : n ≤ m)
    (F : Fin (Volume P m G S) → Bit) :
    eraseFile P n m G S B (canonical B hB F) =
      some (canonical B hB (fun y => F (physicalEmbed h y)),
        (Volume P m G S+B-1)/B+(Volume P n G S+B-1)/B) := by
  obtain ⟨out,hr,ho,hc,_,_⟩ := BinaryPaddingScan.erase_physical h (0 : Bit) B hB F
    (canonical B hB F) (StreamCopy.pack_reader_valid B hB _)
    (by simp only [canonical,flatten_pack,List.ofFn_eq_map])
  simp only [eraseFile,hr,Option.map_some]
  apply congrArg some
  apply Prod.ext
  · simpa only [canonical,List.ofFn_eq_map] using ho
  · simpa only [canonical_length] using hc

theorem padding_exchange_restrict {P n m G S : ℕ} (h : n ≤ m)
    (F : Fin (Volume P n G S) → Bit) :
    (fun y => exchanged (BinaryPaddingScan.expanded h 0 F) (physicalEmbed h y)) =
      exchanged F := by
  funext y
  simp only [exchanged,physicalEmbed,Equiv.symm_apply_apply,BinaryPaddingScan.expanded]
  simp only [Equiv.symm_apply_apply,← embed_exchange,pad_embed]

/-- The only callback is the actual file transformer, not a semantic
array swap. The next theorem is immediately instantiated by `recursive`. -/
def padded (P n m G S B : ℕ) (inner : File → Option Result)
    (source : File) : Option Result := do
  let inserted ← insertFile P n m G S B source
  let changed ← inner inserted.1
  let erased ← eraseFile P n m G S B changed.1
  return (erased.1,inserted.2+changed.2+erased.2)

theorem padded_correct (P n m G S B : ℕ) (hB : 0 < B) (h : n ≤ m)
    (inner : File → Option Result) (F : Fin (Volume P n G S) → Bit)
    (out : Result)
    (hr : inner (canonical B hB (BinaryPaddingScan.expanded h 0 F)) = some out)
    (ho : out.1 = canonical B hB (exchanged (BinaryPaddingScan.expanded h 0 F))) :
    padded P n m G S B inner (canonical B hB F) =
      some (canonical B hB (exchanged F),out.2+
        2*((Volume P n G S+B-1)/B+(Volume P m G S+B-1)/B)) := by
  simp [padded,insert_correct P n m G S B hB h F,hr,ho,
    erase_correct P n m G S B hB h,padding_exchange_restrict,
    two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def scalarData (f P G S : ℕ) (F : Fin (Volume P (radix^f) G S) → Bit) :
    ScalarData f P G S := F ∘ scalarLayout f P G S

theorem scalar_input (f P G S B : ℕ) (hB : 0 < B)
    (F : Fin (Volume P (radix^f) G S) → Bit) :
    represented (scalarLayout f P G S) B hB (scalarData f P G S F) =
      canonical B hB F := by
  apply congrArg (canonical B hB)
  funext y
  simp only [encoded,scalarData,Function.comp_apply,Equiv.apply_symm_apply]

theorem scalar_exchange (f P G S : ℕ)
    (a : FullAddress (Fin P) (Scalar f) (Fin G) (Fin S)) :
    scalarLayout f P G S (exchange a) =
      lowLayout (exchange (lowLayout.symm (scalarLayout f P G S a))) := by
  unfold scalarLayout
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

theorem scalar_output (f P G S B : ℕ) (hB : 0 < B)
    (F : Fin (Volume P (radix^f) G S) → Bit) :
    represented (scalarLayout f P G S) B hB
      (transport exchangeEquiv (scalarData f P G S F)) =
        canonical B hB (exchanged F) := by
  apply congrArg (canonical B hB)
  funext y
  change F (scalarLayout f P G S (exchange ((scalarLayout f P G S).symm y))) = _
  rw [scalar_exchange,Equiv.apply_symm_apply]
  rfl

def recursive (base cutoff B : ℕ) (hB : 0 < B) (k rows n G S : ℕ)
    (source : File) : Option Result :=
  padded (rows*Parameters.W^k) n (radix^(base*Parameters.m^k)) G S B
    (run base cutoff B hB k rows G S) source

/-- No inner correctness or cost premise remains. The added cost is exactly
the read/write count of the two actual padding scans around this run. -/
theorem recursive_correct_cost (base cutoff B : ℕ) (hB : 0 < B)
    (hbase : (radix^base*radix^base)*B ≤ cutoff+B)
    (k rows n G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (h : n ≤ radix^(base*Parameters.m^k))
    (F : Fin (Volume (rows*Parameters.W^k) n G S) → Bit) :
    ∃ out, recursive base cutoff B hB k rows n G S (canonical B hB F) = some out ∧
      out.1 = canonical B hB (exchanged F) ∧
      out.2 ≤ costBound B cutoff k (volume base k rows G S)+
        2*((Volume (rows*Parameters.W^k) n G S+B-1)/B+
          (volume base k rows G S+B-1)/B) := by
  let E := BinaryPaddingScan.expanded h (0 : Bit) F
  obtain ⟨out,hr,ho,hc⟩ := run_correct_cost base cutoff B hB hbase k rows G S hG hS
    (scalarData _ _ _ _ E) (canonical B hB E)
    (scalar_input _ _ _ _ B hB E).symm
  rw [scalar_output] at ho
  let scans := 2*((Volume (rows*Parameters.W^k) n G S+B-1)/B+
    (volume base k rows G S+B-1)/B)
  refine ⟨(canonical B hB (exchanged F),out.2+scans),?_,rfl,Nat.add_le_add_right hc _⟩
  exact padded_correct _ _ _ _ _ B hB h _ F out hr ho

end
end CodedSorting.PhysicalPaddingExchange
end PhysicalPaddingExchange

section PhysicalChunkLayout
/-! Row-major codecs for a pair of unequal adjacent chunks. The two
selected-chunk views have exactly the same integer cell address as the
original product field. Thus exposing a chunk is not a disk permutation.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace CodedSorting.PhysicalChunkLayout
open Circuit Address RecursiveExchange PhysicalRecursiveExchange PhysicalFieldPacking
open PhysicalRecursiveAdapters BinaryPadding CoordinateScans
noncomputable section

abbrev ProductAddress (P Q R G S : ℕ) :=
  FullAddress (Fin P) (Fin Q × Fin R) (Fin G) (Fin S)

def productShape (P Q R G S : ℕ) : ProductAddress P Q R G S ≃ Addr P (Q*R) G S :=
  CommonAddressLayout.shape (Equiv.refl _) finProdFinEquiv (Equiv.refl _) (Equiv.refl _)

def productLayout (P Q R G S : ℕ) : ProductAddress P Q R G S ≃
    Fin (Volume P (Q*R) G S) :=
  (productShape P Q R G S).trans lowLayout

def headShape (P Q R G S : ℕ) : ProductAddress P Q R G S ≃ Addr P Q (R*G) (R*S) where
  toFun a := ⟨a.prefixCoord,a.high.1,finProdFinEquiv (a.high.2,a.gap),
    a.low.1,finProdFinEquiv (a.low.2,a.suffix)⟩
  invFun a := ⟨a.prefixCoord,(a.high,(finProdFinEquiv.symm a.gap).1),
    (finProdFinEquiv.symm a.gap).2,(a.low,(finProdFinEquiv.symm a.suffix).1),
    (finProdFinEquiv.symm a.suffix).2⟩
  left_inv a := by cases a; simp
  right_inv a := by
    change FullAddress.mk a.prefixCoord a.high
      (finProdFinEquiv (finProdFinEquiv.symm a.gap)) a.low
      (finProdFinEquiv (finProdFinEquiv.symm a.suffix)) = a
    rw [finProdFinEquiv.apply_symm_apply,finProdFinEquiv.apply_symm_apply]

def tailShape (P Q R G S : ℕ) : ProductAddress P Q R G S ≃ Addr (P*Q) R (G*Q) S where
  toFun a := ⟨finProdFinEquiv (a.prefixCoord,a.high.1),a.high.2,
    finProdFinEquiv (a.gap,a.low.1),a.low.2,a.suffix⟩
  invFun a := ⟨(finProdFinEquiv.symm a.prefixCoord).1,
    ((finProdFinEquiv.symm a.prefixCoord).2,a.high),
    (finProdFinEquiv.symm a.gap).1,((finProdFinEquiv.symm a.gap).2,a.low),a.suffix⟩
  left_inv a := by cases a; simp
  right_inv a := by
    change FullAddress.mk (finProdFinEquiv (finProdFinEquiv.symm a.prefixCoord)) a.high
      (finProdFinEquiv (finProdFinEquiv.symm a.gap)) a.low a.suffix = a
    rw [finProdFinEquiv.apply_symm_apply,finProdFinEquiv.apply_symm_apply]

theorem head_volume (P Q R G S : ℕ) :
    Volume P Q (R*G) (R*S) = Volume P (Q*R) G S := by unfold Volume; ring

theorem tail_volume (P Q R G S : ℕ) :
    Volume (P*Q) R (G*Q) S = Volume P (Q*R) G S := by unfold Volume; ring

theorem head_address (P Q R G S : ℕ) (a : ProductAddress P Q R G S) :
    finCongr (head_volume P Q R G S) (lowLayout (headShape P Q R G S a)) =
      productLayout P Q R G S a := by
  apply Fin.ext
  simp only [finCongr_apply_coe,headShape,productLayout,productShape,
    Equiv.trans_apply,CommonAddressLayout.shape,Equiv.coe_fn_mk,Equiv.refl_apply,
    lowLayout_val,finProdFinEquiv]
  ring

theorem tail_address (P Q R G S : ℕ) (a : ProductAddress P Q R G S) :
    finCongr (tail_volume P Q R G S) (lowLayout (tailShape P Q R G S a)) =
      productLayout P Q R G S a := by
  apply Fin.ext
  simp only [finCongr_apply_coe,tailShape,productLayout,productShape,
    Equiv.trans_apply,CommonAddressLayout.shape,Equiv.coe_fn_mk,Equiv.refl_apply,
    lowLayout_val,finProdFinEquiv]
  ring

def headSwitch {P Q R G S : ℕ} (a : ProductAddress P Q R G S) :
    ProductAddress P Q R G S :=
  ⟨a.prefixCoord,(a.low.1,a.high.2),a.gap,(a.high.1,a.low.2),a.suffix⟩

def tailSwitch {P Q R G S : ℕ} (a : ProductAddress P Q R G S) :
    ProductAddress P Q R G S :=
  ⟨a.prefixCoord,(a.high.1,a.low.2),a.gap,(a.low.1,a.high.2),a.suffix⟩

theorem switch_complete {P Q R G S : ℕ} (a : ProductAddress P Q R G S) :
    headSwitch (tailSwitch a) = exchange a := rfl

theorem head_conjugate (P Q R G S : ℕ) (a : ProductAddress P Q R G S) :
    (headShape P Q R G S).symm (exchange (headShape P Q R G S a)) = headSwitch a := by
  simp only [headShape,exchange,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,
    Equiv.symm_apply_apply,headSwitch]

theorem tail_conjugate (P Q R G S : ℕ) (a : ProductAddress P Q R G S) :
    (tailShape P Q R G S).symm (exchange (tailShape P Q R G S a)) = tailSwitch a := by
  simp only [tailShape,exchange,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,
    Equiv.symm_apply_apply,tailSwitch]

theorem head_input (P Q R G S B : ℕ) (hB : 0 < B)
    (F : ProductAddress P Q R G S → Bit) :
    represented lowLayout B hB (F ∘ (headShape P Q R G S).symm) =
      represented (productLayout P Q R G S) B hB F := by
  rw [← represented_cast lowLayout (head_volume P Q R G S)]
  exact represented_regroup _ _ _ (head_address P Q R G S) B hB F

theorem tail_input (P Q R G S B : ℕ) (hB : 0 < B)
    (F : ProductAddress P Q R G S → Bit) :
    represented lowLayout B hB (F ∘ (tailShape P Q R G S).symm) =
      represented (productLayout P Q R G S) B hB F := by
  rw [← represented_cast lowLayout (tail_volume P Q R G S)]
  exact represented_regroup _ _ _ (tail_address P Q R G S) B hB F

theorem head_output (P Q R G S B : ℕ) (hB : 0 < B)
    (F : ProductAddress P Q R G S → Bit) :
    represented lowLayout B hB (transport exchangeEquiv (F ∘ (headShape P Q R G S).symm)) =
      represented (productLayout P Q R G S) B hB (F ∘ headSwitch) := by
  rw [regroup_exchange_file _ _ _ _ (head_address P Q R G S)]
  congr 1
  funext a
  change F ((headShape P Q R G S).symm (exchange (headShape P Q R G S a))) = _
  rw [head_conjugate]
  rfl

theorem tail_output (P Q R G S B : ℕ) (hB : 0 < B)
    (F : ProductAddress P Q R G S → Bit) :
    represented lowLayout B hB (transport exchangeEquiv (F ∘ (tailShape P Q R G S).symm)) =
      represented (productLayout P Q R G S) B hB (F ∘ tailSwitch) := by
  rw [regroup_exchange_file _ _ _ _ (tail_address P Q R G S)]
  congr 1
  funext a
  change F ((tailShape P Q R G S).symm (exchange (tailShape P Q R G S a))) = _
  rw [tail_conjugate]
  rfl

theorem product_input (P Q R G S B : ℕ) (hB : 0 < B)
    (F : Addr P (Q*R) G S → Bit) :
    represented (productLayout P Q R G S) B hB (F ∘ productShape P Q R G S) =
      represented lowLayout B hB F := by
  apply congrArg (canonical B hB)
  funext y
  simp only [encoded,productLayout,Equiv.symm_trans_apply,Function.comp_apply,
    Equiv.apply_symm_apply]

theorem product_output (P Q R G S B : ℕ) (hB : 0 < B)
    (F : Addr P (Q*R) G S → Bit) :
    represented (productLayout P Q R G S) B hB
      (transport exchangeEquiv (F ∘ productShape P Q R G S)) =
        represented lowLayout B hB (transport exchangeEquiv F) := by
  have he : transport exchangeEquiv (F ∘ productShape P Q R G S) =
      (transport exchangeEquiv F) ∘ productShape P Q R G S := rfl
  rw [he,product_input]

end
end CodedSorting.PhysicalChunkLayout
end PhysicalChunkLayout

section PhysicalBorrowLayout
/-! Actual borrow/restore scan outputs in the codecs consumed by the
physical chunk interpreter. Every regrouping preserves the integer address.
-/
set_option autoImplicit false
namespace CodedSorting.PhysicalBorrowLayout
open Circuit Address ArbitraryShapes BorrowScan PhysicalRecursiveExchange
open PhysicalRecursiveAdapters BinaryPadding CoordinateScans ScanProgram
noncomputable section

theorem original_volume (O H L G S : ℕ) :
    Volume O (H*L) G S = BorrowScan.volume O H L G S := by
  unfold Volume BorrowScan.volume
  ring

theorem original_address (O H L G S : ℕ) (a : Orig O H L G S) :
    finCongr (original_volume O H L G S)
      (lowLayout (PhysicalChunkLayout.productShape O H L G S a)) = originalCodec O H L G S a := by
  apply Fin.ext
  rw [originalCodec_val]
  simp [PhysicalChunkLayout.productShape,CommonAddressLayout.shape,lowLayout_val,
    finProdFinEquiv,TriangularStreams.tripleEncode,finCongr] <;> ring

theorem original_input (O H L G S B : ℕ) (hB : 0 < B)
    (F : Addr O (H*L) G S → Bit) :
    represented (originalCodec O H L G S) B hB
      (F ∘ PhysicalChunkLayout.productShape O H L G S) = represented lowLayout B hB F := by
  have hh := represented_regroup (originalCodec O H L G S)
    (lowLayout.trans (finCongr (original_volume O H L G S)))
    (PhysicalChunkLayout.productShape O H L G S) (original_address O H L G S) B hB
    (F ∘ PhysicalChunkLayout.productShape O H L G S)
  rw [represented_cast] at hh
  have he : (F ∘ PhysicalChunkLayout.productShape O H L G S) ∘
      (PhysicalChunkLayout.productShape O H L G S).symm = F := by
    funext a
    simp only [Function.comp_apply,Equiv.apply_symm_apply]
  rw [he] at hh
  exact hh.symm

theorem original_output (O H L G S B : ℕ) (hB : 0 < B)
    (F : Addr O (H*L) G S → Bit) :
    represented (originalCodec O H L G S) B hB
      (transport exchangeEquiv (F ∘ PhysicalChunkLayout.productShape O H L G S)) =
      represented lowLayout B hB (transport exchangeEquiv F) := by
  have he : transport exchangeEquiv (F ∘ PhysicalChunkLayout.productShape O H L G S) =
      (transport exchangeEquiv F) ∘ PhysicalChunkLayout.productShape O H L G S := rfl
  rw [he,original_input]

def prefixCode (O H : ℕ) : (Fin O × Fin H × Fin H) ≃ Fin (O*(H*H)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

def borrowedShape (O H L G S : ℕ) : Borrow O H L G S ≃ Addr (O*(H*H)) L G S :=
  CommonAddressLayout.shape (prefixCode O H) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

theorem borrowed_volume (O H L G S : ℕ) :
    Volume (O*(H*H)) L G S = BorrowScan.volume O H L G S := by
  unfold Volume BorrowScan.volume
  ring

theorem borrowed_address (O H L G S : ℕ) (a : Borrow O H L G S) :
    finCongr (borrowed_volume O H L G S) (lowLayout (borrowedShape O H L G S a)) =
      borrowedCodec O H L G S a := by
  apply Fin.ext
  simp [borrowedShape,CommonAddressLayout.shape,lowLayout_val,prefixCode,
    borrowedCodec,borrowedGroup,fourCodec,finProdFinEquiv,TriangularStreams.tripleEncode,finCongr] <;> ring

theorem borrowed_input (O H L G S B : ℕ) (hB : 0 < B)
    (F : Borrow O H L G S → Bit) :
    represented lowLayout B hB (F ∘ (borrowedShape O H L G S).symm) =
      represented (borrowedCodec O H L G S) B hB F := by
  rw [← represented_cast lowLayout (borrowed_volume O H L G S)]
  exact represented_regroup _ _ _ (borrowed_address O H L G S) B hB F

theorem borrowed_output (O H L G S B : ℕ) (hB : 0 < B)
    (F : Borrow O H L G S → Bit) :
    represented lowLayout B hB (transport exchangeEquiv (F ∘ (borrowedShape O H L G S).symm)) =
      represented (borrowedCodec O H L G S) B hB (transport exchangeEquiv F) := by
  rw [regroup_exchange_file _ _ _ _ (borrowed_address O H L G S)]
  congr 1
  funext a
  simp only [RecursiveExchange.viaShape,transport,exchangeEquiv,Equiv.coe_fn_symm_mk,
    borrowedShape,CommonAddressLayout.shape,Equiv.coe_fn_mk,Equiv.refl_apply,
    exchange,Function.comp_apply,Equiv.symm_apply_apply,Equiv.refl_symm]

theorem borrow_run (O q ρ L G S B : ℕ) (hB : 0 < B)
    (F : Orig O (q^ρ) L G S → Bit) :
    ∃ cost, executeProgram B hB (borrowProgram O q ρ L G S)
        (represented (originalCodec O (q^ρ) L G S) B hB F) =
      some (represented (borrowedCodec O (q^ρ) L G S) B hB (move borrowEquiv F),cost) ∧
      cost ≤ ρ*(2*q+6)*(BorrowScan.volume O (q^ρ) L G S/B+1) := by
  obtain ⟨cost,hr,_,hc⟩ := executeProgram_exists B hB (borrowProgram O q ρ L G S)
    (encoded (originalCodec O (q^ρ) L G S) F)
  have he : eval (borrowProgram O q ρ L G S) (encoded (originalCodec O (q^ρ) L G S) F) =
      encoded (borrowedCodec O (q^ρ) L G S) (move borrowEquiv F) := by
    funext y
    rw [eval_eq_pullback,borrowProgram_destination]
    simp only [borrowPermutation,Equiv.symm_trans_apply,Equiv.symm_symm,
      encoded,move,Function.comp_apply,Equiv.symm_apply_apply]
  refine ⟨cost,?_,?_⟩
  · exact hr.trans (congrArg some (congrArg (fun xs => (xs,cost)) (congrArg (canonical B hB) he)))
  · simpa only [borrowProgram_constant] using hc

theorem finish_run (O q ρ L G S B : ℕ) (hB : 0 < B)
    (F : Borrow O (q^ρ) L G S → Bit) :
    ∃ cost, executeProgram B hB (finishProgram O q ρ L G S)
        (represented (borrowedCodec O (q^ρ) L G S) B hB F) =
      some (represented (originalCodec O (q^ρ) L G S) B hB (move finishEquiv F),cost) ∧
      cost ≤ ρ*(2*q+6)*(BorrowScan.volume O (q^ρ) L G S/B+1) := by
  obtain ⟨cost,hr,_,hc⟩ := executeProgram_exists B hB (finishProgram O q ρ L G S)
    (encoded (borrowedCodec O (q^ρ) L G S) F)
  have he : eval (finishProgram O q ρ L G S) (encoded (borrowedCodec O (q^ρ) L G S) F) =
      encoded (originalCodec O (q^ρ) L G S) (move finishEquiv F) := by
    funext y
    rw [eval_eq_pullback,finishProgram_destination]
    simp only [finishPermutation,Equiv.symm_trans_apply,Equiv.symm_symm,
      encoded,move,Function.comp_apply,Equiv.symm_apply_apply]
  refine ⟨cost,?_,?_⟩
  · exact hr.trans (congrArg some (congrArg (fun xs => (xs,cost)) (congrArg (canonical B hB) he)))
  · simpa only [finishProgram_constant] using hc

end
end CodedSorting.PhysicalBorrowLayout
end PhysicalBorrowLayout
