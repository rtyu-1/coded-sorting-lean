import CodedSorting.Interchange.Framework.Memory.PhysicalPaddingExchange

section PhysicalChunkExchange
/-! An arbitrary list of unequal-width chunks is executed on one successive
physical file. Every chunk invokes the verified recursive file interpreter.
No selected-chunk semantic oracle or free physical permutation is used.
Prefix divisibility and base startup are the explicit numerical premises;
borrowing/padding instantiate them in the enclosing arbitrary-width routine.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace CodedSorting.PhysicalChunkExchange
open Circuit Address RecursiveExchange PhysicalRecursiveExchange PhysicalFieldPacking
open PhysicalExchangeRecursion PhysicalPaddingExchange PhysicalChunkLayout
open BinaryPadding CoordinateScans
noncomputable section

abbrev Call := ArbitraryRecursive.Call

def fieldCount : List Call → ℕ
  | [] => 1
  | c::cs => radix^c.width*fieldCount cs

theorem fieldCount_pos (cs : List Call) : 0 < fieldCount cs := by
  induction cs with
  | nil => exact Nat.zero_lt_one
  | cons c cs ih => exact Nat.mul_pos (pow_pos radix_prime.pos _) ih

theorem fieldCount_width (cs : List Call) :
    fieldCount cs = radix^(cs.map ArbitraryRecursive.Call.width).sum := by
  induction cs with
  | nil => simp [fieldCount]
  | cons c cs ih => simp only [fieldCount,List.map_cons,List.sum_cons,pow_add,ih]

def one (cutoff B : ℕ) (hB : 0 < B) (c : Call) (P G S : ℕ)
    (source : File) : Option Result :=
  run c.baseWidth cutoff B hB c.depth (P/Parameters.W^c.depth) G S source

theorem one_correct_cost (cutoff B : ℕ) (hB : 0 < B) (c : Call) (P G S : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hfit : Parameters.W^c.depth ∣ P)
    (hbase : (radix^c.baseWidth*radix^c.baseWidth)*B ≤ cutoff+B)
    (F : Addr P (radix^c.width) G S → Bit) :
    ∃ out, one cutoff B hB c P G S (represented lowLayout B hB F) = some out ∧
      out.1 = represented lowLayout B hB (transport exchangeEquiv F) ∧
      out.2 ≤ costBound B cutoff c.depth (Volume P (radix^c.width) G S) := by
  have hp : P/Parameters.W^c.depth*Parameters.W^c.depth = P := Nat.div_mul_cancel hfit
  have hall : ∀ E : Fin (Volume
      (P/Parameters.W^c.depth*Parameters.W^c.depth) (radix^c.width) G S) → Bit,
      ∃ out,
        one cutoff B hB c P G S (canonical B hB E) = some out ∧
        out.1 = canonical B hB (exchanged E) ∧
        out.2 ≤ costBound B cutoff c.depth
          (Volume (P/Parameters.W^c.depth*Parameters.W^c.depth) (radix^c.width) G S) := by
    intro E
    obtain ⟨out,hr,ho,hc⟩ := run_correct_cost c.baseWidth cutoff B hB hbase c.depth
      (P/Parameters.W^c.depth) G S hG hS (scalarData _ _ _ _ E) (canonical B hB E)
      (scalar_input _ _ _ _ B hB E).symm
    rw [scalar_output] at ho
    exact ⟨out,hr,ho,hc⟩
  rw [hp] at hall
  obtain ⟨out,hr,ho,hc⟩ := hall (encoded lowLayout F)
  refine ⟨out,hr,?_,hc⟩
  rw [ho]
  apply congrArg (canonical B hB)
  funext y
  simp only [exchanged,encoded,Function.comp_apply,Equiv.symm_apply_apply]
  rfl

def execute (cutoff B : ℕ) (hB : 0 < B) :
    List Call → (P G S : ℕ) → File → Option Result
  | [],_,_,_,source => some (source,0)
  | c::cs,P,G,S,source => do
      let head ← one cutoff B hB c P (fieldCount cs*G) (fieldCount cs*S) source
      let tail ← execute cutoff B hB cs (P*radix^c.width) (G*radix^c.width) S head.1
      return (tail.1,head.2+tail.2)

def totalBound (cutoff B : ℕ) (cs : List Call) (V : ℕ) : ℕ :=
  (cs.map fun c => costBound B cutoff c.depth V).sum

theorem execute_correct_cost (cutoff B : ℕ) (hB : 0 < B) (cs : List Call)
    (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (hfit : ∀ c ∈ cs, Parameters.W^c.depth ∣ P)
    (hbase : ∀ c ∈ cs, (radix^c.baseWidth*radix^c.baseWidth)*B ≤ cutoff+B)
    (F : Addr P (fieldCount cs) G S → Bit) :
    ∃ out, execute cutoff B hB cs P G S (represented lowLayout B hB F) = some out ∧
      out.1 = represented lowLayout B hB (transport exchangeEquiv F) ∧
      out.2 ≤ totalBound cutoff B cs (Volume P (fieldCount cs) G S) := by
  induction cs generalizing P G S with
  | nil =>
      refine ⟨(represented lowLayout B hB F,0),rfl,?_,by simp [totalBound]⟩
      change represented lowLayout B hB F = represented lowLayout B hB (transport exchangeEquiv F)
      apply congrArg (represented lowLayout B hB)
      funext a
      have hi : a.high=a.low := @Subsingleton.elim (Fin 1) inferInstance _ _
      cases a
      simp only [transport,exchangeEquiv,Equiv.coe_fn_symm_mk,exchange]
      cases hi
      rfl
  | cons c cs ih =>
      let Q := radix^c.width
      let R := fieldCount cs
      let data : ProductAddress P Q R G S → Bit := F ∘ productShape P Q R G S
      let headData := data ∘ (headShape P Q R G S).symm
      have hhead : 0 < R := fieldCount_pos cs
      have hQ : 0 < Q := pow_pos radix_prime.pos _
      obtain ⟨head,hh,hho,hhc⟩ := one_correct_cost cutoff B hB c P (R*G) (R*S)
        (Nat.mul_pos hhead hG) (Nat.mul_pos hhead hS) (hfit c (by simp))
        (hbase c (by simp)) headData
      have hin : represented lowLayout B hB headData = represented lowLayout B hB F := by
        exact (head_input P Q R G S B hB data).trans (product_input P Q R G S B hB F)
      have hout : head.1=represented (productLayout P Q R G S) B hB (data ∘ headSwitch) :=
        hho.trans (head_output P Q R G S B hB data)
      let tailData := (data ∘ headSwitch) ∘ (tailShape P Q R G S).symm
      obtain ⟨tail,ht,hto,htc⟩ := ih (P*Q) (G*Q) S (Nat.mul_pos hG hQ) hS
        (fun c' hc' => dvd_mul_of_dvd_left (hfit c' (by simp [hc'])) Q)
        (fun c' hc' => hbase c' (by simp [hc'])) tailData
      have htin : represented lowLayout B hB tailData=head.1 :=
        (tail_input P Q R G S B hB (data ∘ headSwitch)).trans hout.symm
      have htout : tail.1 = represented lowLayout B hB (transport exchangeEquiv F) := by
        calc
          tail.1 = represented (productLayout P Q R G S) B hB
              ((data ∘ headSwitch) ∘ tailSwitch) :=
            hto.trans (tail_output P Q R G S B hB (data ∘ headSwitch))
          _ = represented (productLayout P Q R G S) B hB (transport exchangeEquiv data) := rfl
          _ = _ := product_output P Q R G S B hB F
      refine ⟨(tail.1,head.2+tail.2),?_,htout,?_⟩
      · rw [hin] at hh
        rw [htin] at ht
        dsimp only [Q,R] at hh ht
        simp [execute,hh,ht]
      · rw [head_volume] at hhc
        rw [tail_volume] at htc
        exact Nat.add_le_add hhc htc

end
end CodedSorting.PhysicalChunkExchange
end PhysicalChunkExchange

section PhysicalPrefixPadding
/-! Appending and removing complete padding rows are real streaming
operations on the current file, with their exact read/write counts. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalPrefixPadding
open Circuit Address PhysicalRecursiveExchange PhysicalExchangeRecursion
open BinaryPadding CoordinateScans BucketMachine BucketReader
noncomputable section

def expanded {N M : ℕ} (F : Fin N → Bit) (y : Fin M) : Bit :=
  if h : y.val<N then F ⟨y.val,h⟩ else 0

def mask (N M : ℕ) (y : Fin M) : Bool := decide (y.val<N)

theorem prefix_sequence (N M : ℕ) (h : N ≤ M) :
    (List.finRange M).filter (mask N M) = (List.finRange N).map (Fin.castLE h) := by
  have hs : List.Sorted (· < ·) ((List.finRange N).map (Fin.castLE h)) := by
    rw [List.Sorted,List.pairwise_map]
    exact (List.pairwise_lt_finRange N).imp (fun hxy => hxy)
  apply List.Sorted.eq_of_mem_iff ((List.pairwise_lt_finRange M).filter _) hs
  intro y
  simp only [List.mem_filter,List.mem_finRange,true_and,mask,decide_eq_true_eq,List.mem_map]
  constructor
  · intro hy
    exact ⟨⟨y.val,hy⟩,rfl⟩
  · rintro ⟨x,rfl⟩
    exact x.isLt

theorem expanded_cast {N M : ℕ} (h : N ≤ M) (F : Fin N → Bit) (x : Fin N) :
    expanded (M:=M) F (x.castLE h) = F x := by simp [expanded,x.isLt]

def insertFile (N M B : ℕ) (source : File) : Option Result :=
  (StreamMask.insert (BinaryPaddingScan.maskNat (mask N M)) (0 : Bit) B M 0
    ⟨Reader.fromDisk source,Writer.empty⟩).map
      (fun out => (out.target.finish,out.source.reads+out.target.finish.length))

def eraseFile (N M B : ℕ) (source : File) : Option Result :=
  (StreamMask.erase (BinaryPaddingScan.maskNat (mask N M)) B M 0
    ⟨Reader.fromDisk source,Writer.empty⟩).map
      (fun out => (out.target.finish,out.source.reads+out.target.finish.length))

theorem insert_correct (N M B : ℕ) (hB : 0 < B) (h : N ≤ M) (F : Fin N → Bit) :
    insertFile N M B (canonical B hB F) =
      some (canonical B hB (expanded (M:=M) F),(N+B-1)/B+(M+B-1)/B) := by
  have hkept : StreamMask.kept (BinaryPaddingScan.maskNat (mask N M))
      (BinaryPaddingScan.extendNat 0 (expanded (M:=M) F)) M 0 = List.ofFn F := by
    rw [BinaryPaddingScan.finite_kept,prefix_sequence N M h,List.map_map,List.ofFn_eq_map]
    simp only [Function.comp_def,expanded_cast]
  have hpadded : StreamMask.padded (BinaryPaddingScan.maskNat (mask N M)) 0
      (BinaryPaddingScan.extendNat 0 (expanded (M:=M) F)) M 0 =
        List.ofFn (expanded (M:=M) F) := by
    rw [StreamMask.padded,BinaryPaddingScan.finite_positions,List.map_map,List.ofFn_eq_map]
    apply List.map_congr_left
    intro y _
    simp only [Function.comp_def,BinaryPaddingScan.maskNat_at,BinaryPaddingScan.extendNat_at,mask]
    by_cases hy : y.val<N <;> simp [hy,expanded]
  obtain ⟨out,hr,_,ho,hc,_⟩ := StreamMask.insert_file (BinaryPaddingScan.maskNat (mask N M))
    (0 : Bit) B M hB (BinaryPaddingScan.extendNat 0 (expanded (M:=M) F))
    (canonical B hB F) (StreamCopy.pack_reader_valid B hB _)
    (by rw [hkept]; exact flatten_pack B hB _)
  simp only [insertFile,hr,Option.map_some]
  apply congrArg some
  apply Prod.ext
  · exact ho.trans (congrArg (pack B hB) hpadded)
  · simpa only [PhysicalPaddingExchange.canonical_length] using hc

theorem erase_correct (N M B : ℕ) (hB : 0 < B) (h : N ≤ M) (F : Fin M → Bit) :
    eraseFile N M B (canonical B hB F) =
      some (canonical B hB (fun y : Fin N => F (y.castLE h)),(M+B-1)/B+(N+B-1)/B) := by
  have hkept : StreamMask.kept (BinaryPaddingScan.maskNat (mask N M))
      (BinaryPaddingScan.extendNat 0 F) M 0 = List.ofFn (fun y : Fin N => F (y.castLE h)) := by
    rw [BinaryPaddingScan.finite_kept,prefix_sequence N M h,List.map_map,List.ofFn_eq_map]
    rfl
  obtain ⟨out,hr,_,ho,hc,_⟩ := StreamMask.erase_file (BinaryPaddingScan.maskNat (mask N M))
    B M hB (BinaryPaddingScan.extendNat 0 F) (canonical B hB F)
    (StreamCopy.pack_reader_valid B hB _)
    (by rw [BinaryPaddingScan.finite_values,← List.ofFn_eq_map]; exact flatten_pack B hB _)
  simp only [eraseFile,hr,Option.map_some]
  apply congrArg some
  apply Prod.ext
  · exact ho.trans (congrArg (pack B hB) hkept)
  · simpa only [hkept,List.length_ofFn,PhysicalPaddingExchange.canonical_length] using hc

def embed {P P' Q G S : ℕ} (h : P ≤ P') (a : Addr P Q G S) : Addr P' Q G S :=
  ⟨a.prefixCoord.castLE h,a.high,a.gap,a.low,a.suffix⟩

theorem volume_mono {P P' Q G S : ℕ} (h : P ≤ P') : Volume P Q G S ≤ Volume P' Q G S :=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)

theorem embed_address {P P' Q G S : ℕ} (h : P ≤ P') (a : Addr P Q G S) :
    lowLayout (embed h a) = (lowLayout a).castLE (volume_mono h) := by
  apply Fin.ext
  rfl

theorem embed_exchange {P P' Q G S : ℕ} (h : P ≤ P') (a : Addr P Q G S) :
    embed h (exchange a) = exchange (embed h a) := rfl

theorem exchange_restrict {P P' Q G S : ℕ} (h : P ≤ P')
    (F : Fin (Volume P Q G S) → Bit) :
    (fun y => PhysicalPaddingExchange.exchanged (expanded (M:=Volume P' Q G S) F)
        (y.castLE (volume_mono h))) = PhysicalPaddingExchange.exchanged F := by
  funext y
  have hy : lowLayout (embed h (lowLayout.symm y : Addr P Q G S)) =
      y.castLE (volume_mono h) := by simpa using embed_address h (lowLayout.symm y : Addr P Q G S)
  rw [← hy,PhysicalPaddingExchange.exchanged,
    Equiv.symm_apply_apply,← embed_exchange,embed_address,expanded_cast]
  rfl

end
end CodedSorting.PhysicalPrefixPadding
end PhysicalPrefixPadding

section PhysicalChunkBound
/-! Sum the already established costs of the actual chunk interpreter.
There is no per-operation cost oracle: each summand is the physical
recursive runner's own proven recurrence. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalChunkBound
open Circuit RecursiveExchange PhysicalExchangeRecursion PhysicalChunkExchange
open PhysicalRecursionBound ArbitrarySchedule
noncomputable section

def ratio : ℝ := (Parameters.m : ℝ)^(1-(Parameters.epsilon : ℝ))

theorem ratio_gt_one : 1 < ratio := by
  apply Real.one_lt_rpow
  · norm_num [Parameters.m_value]
  · have h : (Parameters.epsilon : ℝ)<1 := by exact_mod_cast Parameters.epsilon_lt_one
    linarith

theorem ratio_power (k : ℕ) :
    (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ))) = ratio^k := by
  rw [mul_comm,Real.rpow_mul_natCast (by positivity)]
  rfl

def weight (cs : List Call) : ℝ := (cs.map fun c => ratio^c.depth).sum

theorem totalBound_improved (cutoff B V : ℕ) (hB : 0 < B)
    (hcut : Parameters.W*B ≤ cutoff) (cs : List Call) :
    (totalBound cutoff B cs V : ℝ) ≤ boundConstant*(1+(V : ℝ)/B)*weight cs := by
  induction cs with
  | nil => simp [totalBound,weight]
  | cons c cs ih =>
      have hcost := costBound_transfers B cutoff c.depth V hB hcut
      rw [ratio_power] at hcost
      have hp : (1 : ℝ) ≤ ratio^c.depth := one_le_pow₀ ratio_gt_one.le
      have hfactor : 0 ≤ boundConstant := boundConstant_nonneg
      have hstep : (costBound B cutoff c.depth V : ℝ) ≤
          boundConstant*(1+(V : ℝ)/B)*ratio^c.depth := by
        have hh := mul_le_mul_of_nonneg_left
          (show 1+(V : ℝ)/B*ratio^c.depth ≤ (1+(V : ℝ)/B)*ratio^c.depth by nlinarith) hfactor
        simpa only [mul_assoc] using hcost.trans hh
      simp only [totalBound,List.map_cons,List.sum_cons,Nat.cast_add,
        weight] at ih ⊢
      nlinarith

theorem calls_weight (base k e : ℕ) :
    weight (ArbitraryRecursive.calls base k e) =
      scaleWeight ratio (scales Parameters.m k (e/base))+1 := by
  simp only [weight,ArbitraryRecursive.calls,List.map_append,List.sum_append,
    List.map_map,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Function.comp_apply,pow_zero,add_zero,scaleWeight]
  rfl

theorem calls_weight_bound (base k e : ℕ) (he : e/base < Parameters.m^(k+1)) :
    weight (ArbitraryRecursive.calls base k e) ≤ Parameters.m * geometric ratio k := by
  rw [calls_weight]
  have hm : 1 < Parameters.m := by norm_num [Parameters.m_value]
  have hs := scaleWeight_bound Parameters.m k (e/base) hm he ratio
    (by have := ratio_gt_one; linarith)
  have hg := depth_le_geometric ratio ratio_gt_one.le k
  have hg1 : (1 : ℝ) ≤ geometric ratio k :=
    (show (1 : ℝ) ≤ (k+1 : ℕ) by exact_mod_cast (by omega : 1 ≤ k+1)).trans hg
  have hcast : ((Parameters.m-1 : ℕ) : ℝ) = Parameters.m-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  rw [hcast] at hs
  nlinarith

theorem calls_totalBound (cutoff B V base k e : ℕ) (hB : 0 < B)
    (hcut : Parameters.W*B ≤ cutoff) (he : e/base < Parameters.m^(k+1)) :
    (totalBound cutoff B (ArbitraryRecursive.calls base k e) V : ℝ) ≤
      boundConstant*(1+(V : ℝ)/B)*Parameters.m*geometric ratio k := by
  have hC : 0 ≤ boundConstant*(1+(V : ℝ)/B) :=
    mul_nonneg boundConstant_nonneg (by positivity)
  have hs := mul_le_mul_of_nonneg_left (calls_weight_bound base k e he) hC
  exact (totalBound_improved cutoff B V hB hcut _).trans (by simpa only [mul_assoc] using hs)

end
end CodedSorting.PhysicalChunkBound
end PhysicalChunkBound

section PhysicalPaddedChunks
/-! Prefix divisibility is enforced by two actual scans surrounding the
complete chunk interpreter. Padding is erased only after all chunks finish.
-/
set_option autoImplicit false
namespace CodedSorting.PhysicalPaddedChunks
open Circuit Address RecursiveExchange PhysicalRecursiveExchange PhysicalExchangeRecursion
open PhysicalChunkExchange BinaryPadding CoordinateScans
noncomputable section

theorem represented_numeric {A : Type} {V : ℕ} (layout : A ≃ Fin V)
    (B : ℕ) (hB : 0 < B) (F : Fin V → Bit) :
    represented layout B hB (F ∘ layout) = canonical B hB F := by
  apply congrArg (canonical B hB)
  funext y
  simp only [encoded,Function.comp_apply,Equiv.apply_symm_apply]

theorem represented_exchanged (P Q G S B : ℕ) (hB : 0 < B)
    (F : Fin (Volume P Q G S) → Bit) :
    represented lowLayout B hB (transport exchangeEquiv (F ∘ lowLayout)) =
      canonical B hB (PhysicalPaddingExchange.exchanged F) := rfl

def execute (cutoff B : ℕ) (hB : 0 < B) (cs : List Call)
    (P P' G S : ℕ) (source : File) : Option Result := do
  let inserted ← PhysicalPrefixPadding.insertFile
    (Volume P (fieldCount cs) G S) (Volume P' (fieldCount cs) G S) B source
  let changed ← PhysicalChunkExchange.execute cutoff B hB cs P' G S inserted.1
  let erased ← PhysicalPrefixPadding.eraseFile
    (Volume P (fieldCount cs) G S) (Volume P' (fieldCount cs) G S) B changed.1
  return (erased.1,inserted.2+changed.2+erased.2)

theorem execute_correct_cost (cutoff B : ℕ) (hB : 0 < B) (cs : List Call)
    (P P' G S : ℕ) (hG : 0 < G) (hS : 0 < S) (hp : P ≤ P')
    (hfit : ∀ c ∈ cs, Parameters.W^c.depth ∣ P')
    (hbase : ∀ c ∈ cs, (radix^c.baseWidth*radix^c.baseWidth)*B ≤ cutoff+B)
    (F : Fin (Volume P (fieldCount cs) G S) → Bit) :
    ∃ out, execute cutoff B hB cs P P' G S (canonical B hB F) = some out ∧
      out.1 = canonical B hB (PhysicalPaddingExchange.exchanged F) ∧
      out.2 ≤ totalBound cutoff B cs (Volume P' (fieldCount cs) G S)+
        2*((Volume P (fieldCount cs) G S+B-1)/B+
          (Volume P' (fieldCount cs) G S+B-1)/B) := by
  let E := PhysicalPrefixPadding.expanded (M:=Volume P' (fieldCount cs) G S) F
  obtain ⟨out,hr,ho,hc⟩ := PhysicalChunkExchange.execute_correct_cost cutoff B hB cs P' G S
    hG hS hfit hbase (E ∘ lowLayout)
  rw [represented_numeric] at hr
  rw [represented_exchanged] at ho
  let scans := 2*((Volume P (fieldCount cs) G S+B-1)/B+
    (Volume P' (fieldCount cs) G S+B-1)/B)
  refine ⟨(canonical B hB (PhysicalPaddingExchange.exchanged F),out.2+scans),?_,rfl,
    Nat.add_le_add_right hc _⟩
  dsimp only [E] at hr ho
  simp [execute,PhysicalPrefixPadding.insert_correct _ _ B hB
    (PhysicalPrefixPadding.volume_mono hp) F,hr,ho,
    PhysicalPrefixPadding.erase_correct _ _ B hB (PhysicalPrefixPadding.volume_mono hp),
    PhysicalPrefixPadding.exchange_restrict hp F,scans,two_mul,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem calls_fit (P base k e : ℕ) :
    ∀ c ∈ ArbitraryRecursive.calls base k e,
      Parameters.W^c.depth ∣ ArbitraryRecursive.paddedRows P k := by
  intro c hc
  obtain ⟨i,hi⟩ := List.get_of_mem hc
  rw [← hi]
  exact ArbitraryRecursive.automatic_calls_fit P base k e i

theorem calls_base (base k e : ℕ) (hbase : 0 < base) :
    ∀ c ∈ ArbitraryRecursive.calls base k e, c.baseWidth ≤ base := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
    rfl
  · have hc : c=⟨e%base,0⟩ := by simpa using h
    rw [hc]
    exact (Nat.mod_lt e hbase).le

theorem calls_startup (base cutoff B k e : ℕ) (hbase : 0 < base)
    (hstartup : (radix^base*radix^base)*B ≤ cutoff+B) :
    ∀ c ∈ ArbitraryRecursive.calls base k e,
      (radix^c.baseWidth*radix^c.baseWidth)*B ≤ cutoff+B := by
  intro c hc
  have hpow := Nat.pow_le_pow_right radix_prime.pos (calls_base base k e hbase c hc)
  exact (Nat.mul_le_mul_right B (Nat.mul_le_mul hpow hpow)).trans hstartup

end
end CodedSorting.PhysicalPaddedChunks
end PhysicalPaddedChunks

section PhysicalBorrowedChunks
/-! One file program for high-digit borrowing, row padding, every genuine
recursive chunk call, removal of row padding, and restoration of high digits.
The cost sums these actual runs and all returned files flow to their successor.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace CodedSorting.PhysicalBorrowedChunks
open Circuit Address RecursiveExchange ArbitraryShapes BorrowScan
open PhysicalRecursiveExchange PhysicalExchangeRecursion PhysicalChunkExchange
open PhysicalBorrowLayout BinaryPadding CoordinateScans
noncomputable section

def execute (cutoff B : ℕ) (hB : 0 < B) (cs : List Call)
    (O ρ P' G S : ℕ) (source : File) : Option Result := do
  let borrowed ← executeProgram B hB (borrowProgram O radix ρ (fieldCount cs) G S) source
  let changed ← PhysicalPaddedChunks.execute cutoff B hB cs
    (O*((radix^ρ)*(radix^ρ))) P' G S borrowed.1
  let restored ← executeProgram B hB (finishProgram O radix ρ (fieldCount cs) G S) changed.1
  return (restored.1,borrowed.2+changed.2+restored.2)

def bound (cutoff B : ℕ) (cs : List Call) (O ρ P' G S : ℕ) : ℕ :=
  totalBound cutoff B cs (Volume P' (fieldCount cs) G S)+
    2*((BorrowScan.volume O (radix^ρ) (fieldCount cs) G S+B-1)/B+
      (Volume P' (fieldCount cs) G S+B-1)/B)+
    2*(ρ*(2*radix+6)*(BorrowScan.volume O (radix^ρ) (fieldCount cs) G S/B+1))

theorem execute_correct_cost (cutoff B : ℕ) (hB : 0 < B) (cs : List Call)
    (O ρ P' G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (hp : O*((radix^ρ)*(radix^ρ)) ≤ P')
    (hfit : ∀ c ∈ cs, Parameters.W^c.depth ∣ P')
    (hbase : ∀ c ∈ cs, (radix^c.baseWidth*radix^c.baseWidth)*B ≤ cutoff+B)
    (F : Orig O (radix^ρ) (fieldCount cs) G S → Bit) :
    ∃ out,
      execute cutoff B hB cs O ρ P' G S
        (represented (originalCodec O (radix^ρ) (fieldCount cs) G S) B hB F) = some out ∧
      out.1 = represented (originalCodec O (radix^ρ) (fieldCount cs) G S) B hB
        (transport exchangeEquiv F) ∧
      out.2 ≤ bound cutoff B cs O ρ P' G S := by
  let L := fieldCount cs
  let H := radix^ρ
  let data : Borrow O H L G S → Bit := move borrowEquiv F
  let innerData := data ∘ (borrowedShape O H L G S).symm
  let E := encoded lowLayout innerData
  obtain ⟨bc,hb,hbc⟩ := borrow_run O radix ρ L G S B hB F
  obtain ⟨middle,hm,hmo,hmc⟩ := PhysicalPaddedChunks.execute_correct_cost cutoff B hB cs
    (O*(H*H)) P' G S hG hS hp hfit hbase E
  have hinput : canonical B hB E=represented (borrowedCodec O H L G S) B hB data :=
    borrowed_input O H L G S B hB data
  have houtput : middle.1=represented (borrowedCodec O H L G S) B hB
      (transport exchangeEquiv data) := by
    apply hmo.trans
    have hfun : canonical B hB (PhysicalPaddingExchange.exchanged E) =
        represented lowLayout B hB (transport exchangeEquiv innerData) := by
      apply congrArg (canonical B hB)
      funext y
      simp only [PhysicalPaddingExchange.exchanged,E,encoded,Function.comp_apply,
        Equiv.symm_apply_apply]
      rfl
    exact hfun.trans (borrowed_output O H L G S B hB data)
  obtain ⟨fc,hf,hfc⟩ := finish_run O radix ρ L G S B hB (transport exchangeEquiv data)
  have hfinal : move finishEquiv (transport exchangeEquiv data) = transport exchangeEquiv F := by
    funext a
    cases a
    rfl
  refine ⟨(represented (originalCodec O H L G S) B hB (transport exchangeEquiv F),
    bc+middle.2+fc),?_,rfl,?_⟩
  · rw [hinput] at hm
    rw [hfinal,← houtput] at hf
    dsimp only [L,H,data] at hb hm hf
    simp [execute,hb,hm,hf,L,H]
  · rw [borrowed_volume] at hmc
    unfold bound
    dsimp [L,H] at hbc hfc hmc ⊢
    omega

def automatic (base cutoff B : ℕ) (hB : 0 < B) (O e G S : ℕ)
    (source : File) : Option Result :=
  let k := ArbitrarySchedule.depth Parameters.m base e
  let ρ := ArbitrarySchedule.borrowedWidth radix Parameters.W k
  let cs := ArbitraryRecursive.calls base k (e-ρ)
  execute cutoff B hB cs O ρ
    (ArbitraryRecursive.paddedRows (O*((radix^ρ)*(radix^ρ))) k) G S source

theorem automatic_correct_cost (base cutoff B : ℕ) (hB : 0 < B)
    (hb : 0 < base) (hstartup : (radix^base*radix^base)*B ≤ cutoff+B)
    (O e G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (F : Orig O
      (radix^(ArbitrarySchedule.borrowedWidth radix Parameters.W (ArbitrarySchedule.depth Parameters.m base e)))
      (fieldCount (ArbitraryRecursive.calls base (ArbitrarySchedule.depth Parameters.m base e)
        (e-ArbitrarySchedule.borrowedWidth radix Parameters.W (ArbitrarySchedule.depth Parameters.m base e))))
      G S → Bit) :
    let k := ArbitrarySchedule.depth Parameters.m base e
    let ρ := ArbitrarySchedule.borrowedWidth radix Parameters.W k
    let cs := ArbitraryRecursive.calls base k (e-ρ)
    let P' := ArbitraryRecursive.paddedRows (O*((radix^ρ)*(radix^ρ))) k
    ∃ out, automatic base cutoff B hB O e G S
        (represented (originalCodec O (radix^ρ) (fieldCount cs) G S) B hB F) = some out ∧
      out.1 = represented (originalCodec O (radix^ρ) (fieldCount cs) G S) B hB
        (transport exchangeEquiv F) ∧ out.2 ≤ bound cutoff B cs O ρ P' G S := by
  dsimp only
  apply execute_correct_cost cutoff B hB _ _ _ _ _ _ hG hS
  · exact ArbitraryRecursive.original_rows_le_padded _ _
  · exact PhysicalPaddedChunks.calls_fit _ _ _ _
  · exact PhysicalPaddedChunks.calls_startup _ _ _ _ _ hb hstartup

end
end CodedSorting.PhysicalBorrowedChunks
end PhysicalBorrowedChunks
