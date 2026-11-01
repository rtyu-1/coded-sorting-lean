import CodedSorting.Shared.Records.Transform
import CodedSorting.Sorting.Local.Framework.CostBound

section MarginsSemantic
/-! The real margin scanner's record operation agrees with the four
boundary operations of the local Columnsort pipeline.  All casts here
preserve the numeric record position. -/
set_option autoImplicit false
namespace CodedSorting.CommonLocalMarginsSemantic
open CommonLocalSemantic CommonStaticMarginsRecords RecursiveColumnsort
open KeyRecordWords (Record)

theorem pad_margin {w n N : ℕ} (hn : n≤N) (f : Fin n → Record w) :
    (fun i : Fin N => margin 0 n (N-n) 0 (by omega) f
      (finCongr (show N=0+n+(N-n) by omega) i))=pad f := by
  funext i
  simp only [margin,Nat.not_lt_zero,Nat.zero_add,Nat.sub_zero,Fin.coe_cast,
    finCongr_apply_coe,dite_false,pad]
  rfl

theorem trim_margin {w n N : ℕ} (hn : n≤N) (f : Fin N → Record w) :
    (fun i : Fin n => margin 0 n 0 0 (by omega) f
      (finCongr (show n=0+n+0 by omega) i))=trim hn f := by
  funext i
  simp only [margin,Nat.not_lt_zero,Nat.zero_add,Nat.sub_zero,finCongr_apply_coe,
    dite_false,dif_pos i.isLt,trim]
  rfl

theorem shift_margin {w : ℕ} (s r h : ℕ) (hr : r=2*h)
    (f : Fin (s*r) → Record w) :
    (fun i : Fin ((s+1)*r) => margin h (s*r) h 0 (by omega) f
      (finCongr (show (s+1)*r=h+s*r+h by rw [hr]; ring) i))=shift s r h f := by
  funext i
  rw [shift_at]
  simp only [margin,finCongr_apply_coe,Nat.zero_add]
  rfl

theorem unshift_margin {w : ℕ} (s r h : ℕ) (hr : r=2*h)
    (f : Fin ((s+1)*r) → Record w) :
    (fun i : Fin (s*r) => margin 0 (s*r) 0 h
      (by rw [hr]; nlinarith) f (finCongr (show s*r=0+s*r+0 by omega) i))=
      unshift s r h f := by
  funext i
  rw [unshift_at s r h hr]
  simp only [margin,Nat.not_lt_zero,Nat.zero_add,Nat.sub_zero,finCongr_apply_coe,
    dite_false,dif_pos i.isLt]

end CodedSorting.CommonLocalMarginsSemantic
end MarginsSemantic

section Node
/-! One complete actual local Columnsort node. The same child-column
program is run three times; the final batch has one additional column.
The two transposes and all four margin scans are actual charged programs. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace CodedSorting.CommonLocalNode
open CommonSortingNormalization CommonStaticSchedule CommonRecordProgram CommonRecordEncoding
open CommonRecordTransform CommonRecordReindex CommonSortingSemanticSwaps CommonLocalSemantic
open RecursiveColumnsort PhysicalLocalSortNode CommonLocalMarginsSemantic
noncomputable section

abbrev side (n : ℕ) := LocalShape.sizeChoice n
abbrev rowCount (n : ℕ) := rows (side n)
abbrev half (n : ℕ) := LocalShape.columnLength n/2
abbrev small (n : ℕ) := side n*rowCount n
abbrev large (n : ℕ) := (side n+1)*rowCount n

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (n source A B work limit : ℕ) (op : Operation (KeyRecordWords.Record q.w))
    (pA : Program q (small n) A work limit (batch op (side n) (rowCount n)))
    (pB : Program q (large n) B work limit (batch op (side n+1) (rowCount n)))
    (pf : Program q (small n) A work limit (forwardAtRows q (side n)))
    (pb : Program q (small n) A work limit (backwardAtRows q (side n)))
    (hs : source+max 1 (recordBlocks q n)≤A)
    (hAB : A+max 1 (recordBlocks q (small n))≤B)
    (hBW : B+max 1 (recordBlocks q (large n))≤work)
    (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (hshape : 3*large n<(2^q.w)^q.digits)
    (hr : rowCount n=2*half n) :
    Program q n source A limit (pipeline op n) := by
  let a := small n
  let b := large n
  let h := half n
  change A+max 1 (recordBlocks q a)≤B at hAB
  change B+max 1 (recordBlocks q b)≤work at hBW
  have hn : n≤a := padded_size n
  have hab : a≤b := by dsimp [a,b,small,large]; nlinarith
  have hh : h≤b := by dsimp [a,b,h,small,large,half] at *; nlinarith
  have hbh : h+a+h=b := by dsimp [a,b,h,small,large]; rw [hr]; ring
  have hcount : ∀ x y : ℕ,x≤y → recordBlocks q x≤recordBlocks q y := by
    intro x y hxy
    apply CommonFinitePadding.count_mono
    exact Nat.mul_le_mul_right _ hxy
  have hna := hcount n a hn
  have habc := hcount a b hab
  have hhc := hcount (h+a) b (by omega)
  have hSA : source+recordBlocks q n≤q.N^q.exponent := by omega
  have hAcap : A+recordBlocks q a≤q.N^q.exponent := by omega
  have hBcap : B+recordBlocks q b≤q.N^q.exponent := by omega
  have hshape' : ∀ L N R O : ℕ,L≤b → N≤b → R≤b → O≤b →
      CommonStaticMargins.ShapeFits q (3*L) (3*N) (3*R) (3*O) := by
    intro L N R O hL hN hR hO
    exact ⟨by omega,by omega,by omega,by omega⟩
  have hwA : A≤work := by omega
  have hAB' : A≤B := by omega
  have hframeA : ∀ x : Fin (q.N^q.exponent),
      (x.val<source ∨ source+recordBlocks q n≤x.val) →
      (x.val<A ∨ limit≤x.val) →x.val<A ∨ A+recordBlocks q a≤x.val := by
    intro x _ hx;rcases hx with hx|hx
    · exact Or.inl hx
    · exact Or.inr (by omega)
  have hframeB : ∀ x : Fin (q.N^q.exponent),
      (x.val<source ∨ source+recordBlocks q n≤x.val) →
      (x.val<A ∨ limit≤x.val) →x.val<B ∨ B+recordBlocks q b≤x.val := by
    intro x _ hx;rcases hx with hx|hx
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  let pad0 := margins q reader 0 n (a-n) 0 source A source n A limit (by omega)
    (hshape' _ _ _ _ (by omega) (by omega) (by omega) (by omega)) hSA
    (by simpa only [Nat.mul_zero,Nat.zero_add,←recordBlocks_eq_words] using
      (show source+max 1 (recordBlocks q n)≤q.N^q.exponent by omega))
    (by convert hAcap using 1 <;> congr 2 <;> omega)
    (Or.inl (by simpa only [Nat.mul_zero,Nat.zero_add,←recordBlocks_eq_words] using hs))
    (by simpa only [Nat.zero_add,Nat.add_sub_of_le hn] using hframeA)
  let padStage : Stage q n a source A source n A limit (pad (N:=a)) :=
    (pad0.castOutput (by omega)).changeFunction (by
      funext f i
      exact congrFun (pad_margin hn f) i)
  let childA : Stage q a a A A source n A limit (batch op (side n) (rowCount n)) :=
    workspaceProgram q pA (by rfl) (by omega) hwA
  let forwardStage : Stage q a a A A source n A limit (forwardAtRows q (side n)) :=
    workspaceProgram q pf (by rfl) (by omega) hwA
  let backwardStage : Stage q a a A A source n A limit (backwardAtRows q (side n)) :=
    workspaceProgram q pb (by rfl) (by omega) hwA
  let shift0 := margins q reader h a h 0 A B source n A limit (by omega)
    (hshape' _ _ _ _ hh hab hh (by omega)) hAcap
    (by simpa only [Nat.mul_zero,Nat.zero_add,←recordBlocks_eq_words] using
      (show A+max 1 (recordBlocks q a)≤q.N^q.exponent by omega))
    (by simpa only [hbh] using hBcap)
    (Or.inl (by simpa only [Nat.mul_zero,Nat.zero_add,←recordBlocks_eq_words] using hAB))
    (by simpa only [hbh] using hframeB)
  let shiftStage : Stage q a b A B source n A limit (shift (side n) (rowCount n) h) :=
    (shift0.castOutput hbh).changeFunction (by
      funext f i
      exact congrFun (shift_margin (side n) (rowCount n) h hr f) i)
  let childB : Stage q b b B B source n A limit (batch op (side n+1) (rowCount n)) :=
    workspaceProgram q pB hAB' (by omega) hwA
  let unshift0 := margins q reader 0 a 0 h B A source n A limit (by omega)
    (hshape' _ _ _ _ (by omega) hab (by omega) hh) hBcap
    (by rw [←Nat.mul_add,←recordBlocks_eq_words];omega)
    (by simpa only [Nat.zero_add,Nat.add_zero] using hAcap)
    (Or.inr (by simpa only [Nat.zero_add,Nat.add_zero] using
      (show A+recordBlocks q a≤B by omega)))
    (by simpa only [Nat.zero_add,Nat.add_zero] using hframeA)
  let unshiftStage : Stage q b a B A source n A limit (unshift (side n) (rowCount n) h) :=
    (unshift0.castOutput (by omega)).changeFunction (by
      funext f i
      exact congrFun (unshift_margin (side n) (rowCount n) h hr f) i)
  let trim0 := margins q reader 0 n 0 0 A source source n A limit (by omega)
    (hshape' _ _ _ _ (by omega) (by omega) (by omega) (by omega)) hAcap
    (by simpa only [Nat.mul_zero,Nat.zero_add,←recordBlocks_eq_words] using
      (show A+max 1 (recordBlocks q n)≤q.N^q.exponent by omega))
    (by simpa only [Nat.zero_add,Nat.add_zero] using hSA)
    (Or.inr (by simpa only [Nat.zero_add,Nat.add_zero] using
      (show source+recordBlocks q n≤A by omega)))
    (by intro x hx _;simpa only [Nat.zero_add,Nat.add_zero] using hx)
  let trimStage : Stage q a n A source source n A limit (trim hn) :=
    (trim0.castOutput (by omega)).changeFunction (by
      funext f i
      exact congrFun (trim_margin hn f) i)
  let all := (((((((((padStage.append childA).append forwardStage).append childA).append
    backwardStage).append childA).append shiftStage).append childB).append unshiftStage).append trimStage)
  have hc : all.charge=3*pA.charge+pB.charge+pf.charge+pb.charge+
      3*(2*recordBlocks q (small n)+recordBlocks q (large n)+recordBlocks q n) := by
    simp only [all,Stage.append_charge,padStage,shiftStage,unshiftStage,trimStage,
      Stage.changeFunction_charge,Stage.castOutput_charge,childA,childB,
      forwardStage,backwardStage,workspaceProgram_charge]
    change 3*recordBlocks q (0+n+(a-n))+pA.charge+pf.charge+pA.charge+pb.charge+
      pA.charge+3*recordBlocks q (h+a+h)+pB.charge+
      3*recordBlocks q (0+a+0)+3*recordBlocks q (0+n+0)=_
    rw [show 0+n+(a-n)=a by omega,hbh]
    simp only [Nat.zero_add,Nat.add_zero]
    change 3*recordBlocks q a+pA.charge+pf.charge+pA.charge+pb.charge+pA.charge+
      3*recordBlocks q b+pB.charge+3*recordBlocks q a+3*recordBlocks q n=
      3*pA.charge+pB.charge+pf.charge+pb.charge+3*(2*recordBlocks q a+recordBlocks q b+recordBlocks q n)
    ring
  let completed : Program q n source A limit (pipeline op n) := all.toProgram.changeFunction (by
    funext f
    simp only [Function.comp_def,pipeline]
    rw [middle_stages])
  exact {
    instructions:=completed.instructions
    charge:=3*pA.charge+pB.charge+pf.charge+pb.charge+
      3*(2*recordBlocks q (small n)+recordBlocks q (large n)+recordBlocks q n)
    correct:=completed.correct
    frame:=completed.frame
    safe:=completed.safe
    cost_le:=by
      have he : completed.charge=all.charge := by
        simp only [completed,CommonRecordReindex.changeFunction_charge,Stage.toProgram_charge]
      exact completed.cost_le.trans_eq (he.trans hc)
    length_le:=by
      have he : completed.charge=all.charge := by
        simp only [completed,CommonRecordReindex.changeFunction_charge,Stage.toProgram_charge]
      exact completed.length_le.trans_eq (he.trans hc)
  }

theorem program_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (n source A B work limit : ℕ) (op : Operation (KeyRecordWords.Record q.w))
    (pA : Program q (small n) A work limit (batch op (side n) (rowCount n)))
    (pB : Program q (large n) B work limit (batch op (side n+1) (rowCount n)))
    (pf : Program q (small n) A work limit (forwardAtRows q (side n)))
    (pb : Program q (small n) A work limit (backwardAtRows q (side n)))
    (hs : source+max 1 (recordBlocks q n)≤A)
    (hAB : A+max 1 (recordBlocks q (small n))≤B)
    (hBW : B+max 1 (recordBlocks q (large n))≤work)
    (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (hshape : 3*large n<(2^q.w)^q.digits)
    (hr : rowCount n=2*half n) :
    (program q reader n source A B work limit op pA pB pf pb hs hAB hBW hwl hl hshape hr).charge=
      3*pA.charge+pB.charge+pf.charge+pb.charge+
        3*(2*recordBlocks q (small n)+recordBlocks q (large n)+recordBlocks q n) := by
  rfl

end
end CodedSorting.CommonLocalNode
end Node

section DescriptorBounds
/-! Explicit sizes of the local sorter's word descriptors.  The expanded
file is at most twice the power-of-two padded volume, so every margin
scan needs fewer than 96 n words at a nonleaf of size n. -/
set_option autoImplicit false
namespace CodedSorting.CommonLocalDescriptorBounds
open CommonSortingNormalization CommonLocalNode PhysicalLocalSortNode
open CommonLocalSemantic SortingResourceBudget

/-- The shifted file adds one column to the padded s by s cubed layout. -/
theorem large_identity (n : ℕ) :
    large n=LocalShape.sizeChoice n^4+LocalShape.sizeChoice n^3 := by
  unfold large side rowCount rows
  ring

theorem rowCount_identity (n : ℕ) : rowCount n=LocalShape.columnLength n := by
  unfold rowCount side rows LocalShape.columnLength
  ring

/-- All three-word margin descriptors satisfy one linear size bound. -/
theorem large_words_lt (n : ℕ) (hn : 1<n) : 3*large n<96*n := by
  have hp := LocalShape.padding_lt n hn
  have hs : 0<LocalShape.sizeChoice n := by unfold LocalShape.sizeChoice; positivity
  have hr : LocalShape.sizeChoice n^3≤LocalShape.sizeChoice n^4 :=
    Nat.pow_le_pow_right hs (by omega)
  rw [large_identity]
  omega

theorem child_lt (n : ℕ) (hn : 512<n) : rowCount n<n := by
  rw [rowCount_identity]
  exact LocalShape.column_lt n hn

/-- The fixed memory reserve leaves much more room than these descriptors use. -/
theorem height_scaled_le_input (q : Configuration) : 96*q.height≤q.N := by
  have hC : 96≤reserve q.inventory q.c q.digits := by
    have h := (reserve_bounds q.inventory q.c q.digits).1
    unfold payloadCoefficient at h
    omega
  have hdiv : q.height*reserve q.inventory q.c q.digits≤q.M := Nat.div_mul_le_self _ _
  have hm := Nat.mul_le_mul_right q.height hC
  nlinarith [q.memory_input]

/-- A quadratic disk exponent already provides enough words for every
margin descriptor of every local problem of at most H squared records. -/
theorem capacity_of_height_squared (q : Configuration) (n : ℕ)
    (hn : n≤q.height^2) (he : 2≤q.exponent) :
    96*max n 1<(2^q.w)^q.digits := by
  have hH : 0<q.height :=
    (normalized_shape q.inventory q.c q.digits q.M q.B q.memory_large
      (by have:=q.block_memory;omega)).1
  have hscale := height_scaled_le_input q
  have hHN : q.height≤q.N := by omega
  have hmax : max n 1≤q.height^2 := by
    apply max_le hn
    nlinarith
  have hproduct := Nat.mul_le_mul hscale hHN
  have hN : 96*max n 1≤q.N^2 := by
    have hm := Nat.mul_le_mul_left 96 hmax
    nlinarith
  have hpow : q.N^2≤q.N^q.exponent :=
    Nat.pow_le_pow_right (by have:=q.input_large;omega) he
  have hcap := WordConvention.polynomial_capacity q.N q.w q.c q.exponent
    q.input_large q.word_convention
  change q.N^q.exponent+1≤(2^q.w)^q.digits at hcap
  omega

/-- The same capacity fact holds for every subproblem of the original input. -/
theorem capacity_of_input (q : Configuration) (n : ℕ)
    (hn : n≤q.N) (he : 2≤q.exponent) :
    96*max n 1<(2^q.w)^q.digits := by
  have hH : 0<q.height :=
    (normalized_shape q.inventory q.c q.digits q.M q.B q.memory_large
      (by have:=q.block_memory;omega)).1
  have hscale := height_scaled_le_input q
  have h96 : 96≤q.N := by nlinarith
  have hmax : max n 1≤q.N := max_le hn (by have:=q.input_large;omega)
  have hproduct := Nat.mul_le_mul h96 hmax
  have hN : 96*max n 1≤q.N^2 := by nlinarith
  have hpow : q.N^2≤q.N^q.exponent :=
    Nat.pow_le_pow_right (by have:=q.input_large;omega) he
  have hcap := WordConvention.polynomial_capacity q.N q.w q.c q.exponent
    q.input_large q.word_convention
  change q.N^q.exponent+1≤(2^q.w)^q.digits at hcap
  omega

end CodedSorting.CommonLocalDescriptorBounds
end DescriptorBounds

section RecursiveProgram
/-! The actual finite-depth local sorter. Every recursive child is built
here, all children share one allocated workspace, and all leaf batches
are implemented by grouped resident computations. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
namespace CodedSorting.CommonLocalRecursion
open CommonSortingNormalization CommonRecordProgram CommonPrunedParameters
open CommonLocalNode CommonLocalSemantic RecursiveColumnsort CommonLocalAdmissible
noncomputable section

/-- Only publicly bounded word descriptors are required by the margin scans. -/
def Descriptors (q : Configuration) : ℕ→ℕ→Prop
  | 0,_ => True
  | fuel+1,n => if n≤512*q.height then True else
      3*large n<(2^q.w)^q.digits ∧ Descriptors q fuel (rowCount n)

def batchSpace (q : Configuration) (c r childSpace : ℕ) : ℕ :=
  if r≤512*q.height then CommonGroupedLeafBatch.space q c r else
    c*recordBlocks q r+childSpace

def space (q : Configuration) (hnormal : Normalized q) : ℕ→ℕ→ℕ
  | 0,n => recordBlocks q n
  | fuel+1,n => if n≤512*q.height then recordBlocks q n else
      max 1 (recordBlocks q (small n))+max 1 (recordBlocks q (large n))+
        max (batchSpace q (side n) (rowCount n) (space q hnormal fuel (rowCount n)))
          (max (batchSpace q (side n+1) (rowCount n) (space q hnormal fuel (rowCount n)))
            (CommonSortingSwaps.space q (LocalShape.sizeExponent n) 3 (by omega) hnormal))

theorem height_pos (q : Configuration) : 0<q.height :=
  (SortingResourceBudget.normalized_shape q.inventory q.c q.digits q.M q.B
    q.memory_large (by have:=q.block_memory; omega)).1

theorem block_le_height (q : Configuration) : q.block≤q.height :=
  (SortingResourceBudget.normalized_shape q.inventory q.c q.digits q.M q.B
    q.memory_large (by have:=q.block_memory; omega)).2.1

def operation (q : Configuration) (fuel : ℕ) : Operation (KeyRecordWords.Record q.w) :=
  returned (localRun q.height (height_pos q) fuel)

theorem small_output (q : Configuration) (fuel n : ℕ) (hn : n≤512*q.height)
    (f : Records q n) : operation q fuel n f=Columnsort.sortColumn f := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [operation,returned,localRun,if_pos hn]

theorem small_batch (q : Configuration) (fuel c r : ℕ) (hr : r≤512*q.height) :
    CommonGroupedLeafBatch.sortColumns (q:=q) c r=batch (operation q fuel) c r := by
  funext f i
  obtain ⟨⟨j,k⟩,rfl⟩ := finProdFinEquiv.surjective i
  simp only [CommonGroupedLeafBatch.sortColumns,CommonSlabBatch.batchOutput,
    PhysicalLocalSortPadding.flattenColumns,Equiv.symm_apply_apply,batch_at,small_output q fuel r hr]

theorem blocks_positive (q : Configuration) (n : ℕ) (hn : 0<n) :
    0<recordBlocks q n := by
  have h := LayoutConversion.blockCount_covers (3*n) q.block (CommonLeafProgram.block_positive q)
  change 3*n≤PhysicalStreamCursor.blockCount q.block (3*n)*q.block at h
  rw [←CommonRecordEncoding.recordBlocks_eq_words] at h
  by_contra hz
  have he : recordBlocks q n=0 := by omega
  rw [he,Nat.zero_mul] at h
  omega


end
end CodedSorting.CommonLocalRecursion
namespace CodedSorting.LocalSorter
open CommonSortingNormalization CommonRecordProgram PhysicalLocalSortNode
open CommonLocalNode CommonLocalSemantic RecursiveColumnsort CommonLocalAdmissible
open CommonLocalRecursion
noncomputable section

/-- The only variable ingredients of the local sorter. The program types
already include their exact permutation, safety, and disk preservation.
Neither sorting correctness nor a successful execution is an assumption. -/
structure Exchange (q : Configuration) where
  condition : Prop
  cost : ℕ → ℕ
  space : ℕ → condition → ℕ
  forward : (reader : Fin q.inventory.readers) → (t source buffer limit : ℕ) →
    (hnormal : condition) →
    source + recordBlocks q ((2^t)*rows (2^t)) ≤ buffer →
    buffer + space t hnormal ≤ limit → limit ≤ q.N^q.exponent →
    Program q ((2^t)*rows (2^t)) source buffer limit
      (CommonSortingSemanticSwaps.forwardAtRows q (2^t))
  backward : (reader : Fin q.inventory.readers) → (t source buffer limit : ℕ) →
    (hnormal : condition) →
    source + recordBlocks q ((2^t)*rows (2^t)) ≤ buffer →
    buffer + space t hnormal ≤ limit → limit ≤ q.N^q.exponent →
    Program q ((2^t)*rows (2^t)) source buffer limit
      (CommonSortingSemanticSwaps.backwardAtRows q (2^t))
  forward_bound : ∀ reader t source buffer limit hnormal hs hw hl,
    (forward reader t source buffer limit hnormal hs hw hl).charge ≤ 3*cost t
  backward_bound : ∀ reader t source buffer limit hnormal hs hw hl,
    (backward reader t source buffer limit hnormal hs hw hl).charge ≤ 3*cost t

abbrev batchBound := CommonLocalBudget.batchBound

def budget (swap : (q : Configuration) → Exchange q) (q : Configuration) : ℕ → ℕ → ℕ
  | 0,n => 8*recordBlocks q n+1
  | fuel+1,n =>
    if n≤512*q.height then 8*recordBlocks q n+1
    else
      let s := LocalShape.sizeChoice n
      let r := rows s
      3*batchBound q (budget swap q fuel r) s r+
        batchBound q (budget swap q fuel r) (s+1) r+
        6*(swap q).cost (LocalShape.sizeExponent n)+
        3*(2*recordBlocks q (s*r)+recordBlocks q ((s+1)*r)+recordBlocks q n)

def space (swap : (q : Configuration) → Exchange q) (q : Configuration) (hnormal : (swap q).condition) : ℕ→ℕ→ℕ
  | 0,n => recordBlocks q n
  | fuel+1,n => if n≤512*q.height then recordBlocks q n else
      max 1 (recordBlocks q (small n))+max 1 (recordBlocks q (large n))+
        max (batchSpace q (side n) (rowCount n) (space swap q hnormal fuel (rowCount n)))
          (max (batchSpace q (side n+1) (rowCount n) (space swap q hnormal fuel (rowCount n)))
            ((swap q).space (LocalShape.sizeExponent n) hnormal))

/-- Internal assembler; the final recursive builder below constructs this
child family rather than taking one as an assumption. -/
def batchBuild (q : Configuration) (reader : Fin q.inventory.readers)
    (fuel c r childSpace childBudget : ℕ)
    (child : ∀ source buffer limit : ℕ,
      source+max 1 (recordBlocks q r)≤buffer → buffer+childSpace≤limit →
      limit≤q.N^q.exponent →
      {p : Program q r source buffer limit (operation q fuel r) // p.charge≤childBudget})
    (source buffer limit : ℕ)
    (hs : source+recordBlocks q (c*r)≤buffer)
    (hw : buffer+batchSpace q c r childSpace≤limit)
    (hl : limit≤q.N^q.exponent) :
    {p : Program q (c*r) source buffer limit (batch (operation q fuel) c r) //
      p.charge≤CommonLocalBudget.batchBound q childBudget c r} := by
  by_cases hr : r≤512*q.height
  · let p := CommonGroupedLeafBatch.program q reader c r source buffer limit hr
      (block_le_height q) hs (by simpa only [batchSpace,if_pos hr] using hw) hl
    refine ⟨p.changeFunction (small_batch q fuel c r hr),?_⟩
    rw [CommonRecordReindex.changeFunction_charge]
    simpa only [CommonLocalBudget.batchBound,if_pos hr] using
      CommonGroupedLeafBatch.program_charge_le q reader c r source buffer limit hr
        (block_le_height q) hs (by simpa only [batchSpace,if_pos hr] using hw) hl
  · let work := buffer+c*recordBlocks q r
    have hwork : work+childSpace≤limit := by
      simpa only [batchSpace,if_neg hr,work,Nat.add_assoc] using hw
    have hwl : work≤limit := by omega
    have hpos : 0<recordBlocks q r := blocks_positive q r (by omega)
    let kids : CommonSlabBatch.Children q c r buffer work limit (operation q fuel r) := fun j =>
      (child (CommonSlabBatch.recordBase q r buffer j.val) work limit
        (by
          rw [max_eq_right hpos]
          have h := CommonSlabBatch.base_end q (C:=c) (n:=r*3) (buffer:=buffer) j
          simpa only [←CommonSlabBatch.record_blocks] using h)
        hwork hl).val
    let p := CommonSlabBatch.program reader kids hs
      (by simp only [←CommonSlabBatch.record_blocks]; exact le_rfl) hwl hl
    refine ⟨p,?_⟩
    have hk : ∀ j : Fin c,(kids j).charge≤childBudget := by
      intro j
      exact (child (CommonSlabBatch.recordBase q r buffer j.val) work limit _ hwork hl).property
    have hsum : CommonSlabBatch.childrenCharge kids (List.finRange c)≤c*childBudget := by
      unfold CommonSlabBatch.childrenCharge
      calc
        _ ≤ ((List.finRange c).map (fun _=>childBudget)).sum := by
          apply List.sum_le_sum
          intro i hi
          exact hk _
        _ = c*childBudget := by simp
    change CommonSlabBatch.childrenCharge kids (List.finRange c)+
      12*(c*CommonSlabBatch.stride q (r*3))≤_
    rw [←CommonSlabBatch.record_blocks]
    simp only [CommonLocalBudget.batchBound,if_neg hr]
    nlinarith

/-- The finite program is constructed by recursion on public fuel.  The
result includes the proved charge, so its use by a parent requires no
assumption about a child execution or a child cost. -/
def build (swap : (q : Configuration) → Exchange q) (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : (swap q).condition) (fuel n : ℕ)
    (ha : Admissible q.height fuel n) (hd : Descriptors q fuel n)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+LocalSorter.space swap q hnormal fuel n≤limit) (hl : limit≤q.N^q.exponent) :
    {p : Program q n source buffer limit (operation q fuel n) //
      p.charge≤LocalSorter.budget swap q fuel n} := by
  induction fuel generalizing n source buffer limit with
  | zero =>
      let p := CommonResidentRecordProgram.program q reader n ha Columnsort.sortColumn source buffer limit
        (by omega) hw hl
      exact ⟨p,by simp only [p,CommonResidentRecordProgram.program_charge,LocalSorter.budget,Nat.le_refl]⟩
  | succ fuel ih =>
      by_cases hn : n≤512*q.height
      · let p := CommonResidentRecordProgram.program q reader n hn Columnsort.sortColumn source buffer limit
          (by omega) (by simpa only [space,if_pos hn] using hw) hl
        refine ⟨p.changeFunction (by funext f; exact (small_output q (fuel+1) n hn f).symm),?_⟩
        rw [CommonRecordReindex.changeFunction_charge]
        simp only [p,CommonResidentRecordProgram.program_charge,LocalSorter.budget,if_pos hn,Nat.le_refl]
      · let r := rowCount n
        let c := side n
        let B := buffer+max 1 (recordBlocks q (small n))
        let work := B+max 1 (recordBlocks q (large n))
        have hadm : Admissible q.height fuel r := by
          have h := CommonLocalAdmissible.child ha (by omega)
          simpa only [r,rowCount,side,rows_eq_columnLength] using h
        have hdesc : 3*large n<(2^q.w)^q.digits ∧ Descriptors q fuel r := by
          simpa only [Descriptors,if_neg hn,r] using hd
        have hrest : work+
            max (batchSpace q c r (LocalSorter.space swap q hnormal fuel r))
              (max (batchSpace q (c+1) r (LocalSorter.space swap q hnormal fuel r))
                ((swap q).space (LocalShape.sizeExponent n) hnormal))≤limit := by
          simpa only [space,if_neg hn,work,B,c,r,Nat.add_assoc] using hw
        have hwl : work≤limit := by omega
        have hwa : work+batchSpace q c r (LocalSorter.space swap q hnormal fuel r)≤limit := by omega
        have hwb : work+batchSpace q (c+1) r (LocalSorter.space swap q hnormal fuel r)≤limit := by omega
        have hwe : work+(swap q).space (LocalShape.sizeExponent n) hnormal≤limit := by omega
        let child := fun (src bf lim : ℕ)
          (hs' : src+max 1 (recordBlocks q r)≤bf)
          (hw' : bf+LocalSorter.space swap q hnormal fuel r≤lim) (hl' : lim≤q.N^q.exponent) =>
          ih r hadm hdesc.2 src bf lim hs' hw' hl'
        have hsepA : buffer+recordBlocks q (c*r)≤work := by
          change buffer+recordBlocks q (small n)≤_
          dsimp only [work,B]
          omega
        have hsepB : B+recordBlocks q ((c+1)*r)≤work := by
          change B+recordBlocks q (large n)≤_
          dsimp only [work]
          omega
        let pa := batchBuild q reader fuel c r (LocalSorter.space swap q hnormal fuel r)
          (LocalSorter.budget swap q fuel r) child buffer work limit hsepA hwa hl
        let pbatch := batchBuild q reader fuel (c+1) r (LocalSorter.space swap q hnormal fuel r)
          (LocalSorter.budget swap q fuel r) child B work limit hsepB hwb hl
        let pf := (swap q).forward reader (LocalShape.sizeExponent n)
          buffer work limit hnormal hsepA hwe hl
        let pb := (swap q).backward reader (LocalShape.sizeExponent n)
          buffer work limit hnormal hsepA hwe hl
        have hr : rowCount n=2*half n := (node_shape n q.height (height_pos q) (by omega)).2.2.1
        let p := CommonLocalNode.program q reader n source buffer B work limit (operation q fuel)
          pa.val pbatch.val pf pb hs le_rfl le_rfl hwl hl hdesc.1 hr
        have he : pipeline (operation q fuel) n=operation q (fuel+1) n := by
          funext f
          rw [show operation q (fuel+1) n f=(nodeRun (localRun q.height (height_pos q) fuel) n f).output by
            simp only [operation,returned,localRun,if_neg hn]]
          exact pipeline_nodeRun (localRun q.height (height_pos q) fuel) n f
        refine ⟨p.changeFunction he,?_⟩
        rw [CommonRecordReindex.changeFunction_charge]
        have hpa := pa.property
        have hpbatch := pbatch.property
        have hpf := (swap q).forward_bound reader (LocalShape.sizeExponent n)
          buffer work limit hnormal hsepA hwe hl
        have hpb := (swap q).backward_bound reader (LocalShape.sizeExponent n)
          buffer work limit hnormal hsepA hwe hl
        change pf.charge≤_ at hpf
        change pb.charge≤_ at hpb
        rw [show p.charge=3*pa.val.charge+pbatch.val.charge+pf.charge+pb.charge+
            3*(2*recordBlocks q (small n)+recordBlocks q (large n)+recordBlocks q n) by
          exact CommonLocalNode.program_charge q reader n source buffer B work limit (operation q fuel)
            pa.val pbatch.val pf pb hs le_rfl le_rfl hwl hl hdesc.1 hr]
        simp only [LocalSorter.budget,if_neg hn]
        change 3*pa.val.charge+pbatch.val.charge+pf.charge+pb.charge+
          3*(2*recordBlocks q (small n)+recordBlocks q (large n)+recordBlocks q n)≤
          3*CommonLocalBudget.batchBound q (LocalSorter.budget swap q fuel r) c r+
          CommonLocalBudget.batchBound q (LocalSorter.budget swap q fuel r) (c+1) r+
          6*(swap q).cost (LocalShape.sizeExponent n)+
          3*(2*recordBlocks q (small n)+recordBlocks q (large n)+recordBlocks q n)
        omega

end
end CodedSorting.LocalSorter
namespace CodedSorting
open CommonSortingNormalization
noncomputable def frameworkLocalExchange (q : Configuration) : LocalSorter.Exchange q where
  condition := CodedSorting.CommonPrunedParameters.Normalized q
  cost t := CodedSorting.CommonSortingSwaps.exchangeCost q t 3
  space t hnormal := CodedSorting.CommonSortingSwaps.space q t 3 (by omega) hnormal
  forward := CodedSorting.CommonSortingSemanticSwaps.forwardProgram q
  backward := CodedSorting.CommonSortingSemanticSwaps.backwardProgram q
  forward_bound := CodedSorting.CommonSortingSemanticSwaps.forward_charge_le q
  backward_bound := CodedSorting.CommonSortingSemanticSwaps.backward_charge_le q
end CodedSorting
namespace CodedSorting.CommonLocalRecursion
noncomputable section
abbrev batchBuild := LocalSorter.batchBuild
def build := LocalSorter.build frameworkLocalExchange
end
end CodedSorting.CommonLocalRecursion
end RecursiveProgram

section Descriptors
/-! The recursive descriptor predicate follows from one public numeric
bound.  For the local input range n ≤ H squared, a quadratic disk exponent
discharges it directly from the machine's existing word convention. -/
set_option autoImplicit false
namespace CodedSorting.CommonLocalDescriptors
open CommonSortingNormalization CommonLocalRecursion CommonLocalNode
open CommonLocalDescriptorBounds

/-- No separate descriptor premise is needed at any recursive descendant. -/
theorem of_capacity (q : Configuration) (fuel n : ℕ)
    (hcap : 96*max n 1<(2^q.w)^q.digits) : Descriptors q fuel n := by
  induction fuel generalizing n with
  | zero => trivial
  | succ fuel ih =>
    by_cases hn : n≤512*q.height
    · simp only [Descriptors,if_pos hn]
    · rw [Descriptors,if_neg hn]
      have hH := height_pos q
      have h512 : 512<n := by nlinarith
      have hchild := child_lt n h512
      refine ⟨?_,ih (rowCount n) ?_⟩
      · exact (large_words_lt n (by omega)).trans_le
          ((Nat.mul_le_mul_left 96 (le_max_left n 1)).trans (Nat.le_of_lt hcap))
      · have hm : max (rowCount n) 1≤max n 1 := max_le_max (by omega) (le_refl _)
        exact (Nat.mul_le_mul_left 96 hm).trans_lt hcap

/-- In the advertised local range, the existing parameter convention
supplies all descriptor bounds with no recursive hypotheses. -/
theorem of_height_squared (q : Configuration) (fuel n : ℕ)
    (hn : n≤q.height^2) (he : 2≤q.exponent) : Descriptors q fuel n :=
  of_capacity q fuel n (capacity_of_height_squared q n hn he)

/-- Every subproblem of the original input also satisfies all recursive
word-descriptor bounds under a quadratic disk exponent. -/
theorem of_input (q : Configuration) (fuel n : ℕ)
    (hn : n≤q.N) (he : 2≤q.exponent) : Descriptors q fuel n :=
  of_capacity q fuel n (capacity_of_input q n hn he)

end CodedSorting.CommonLocalDescriptors
end Descriptors

section Program
/-! Complete local sorting on the common finite RAM/disk machine. The
recursive builder supplies every child and every movement operation.
Workspace and whole-program counter capacity remain explicit resources. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace CodedSorting.LocalSorter.Machine
open CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonLocalRecursion CommonLocalAdmissible CommonPrunedParameters
open CommonLeafProgram (Machine)
noncomputable section
variable (swap : (q : Configuration) → LocalSorter.Exchange q)
attribute [local irreducible] LocalSorter.build
  ControlledNormalization.runLogical

theorem operation_eq_sortColumn (q : Configuration) (fuel n : ℕ) :
    operation q fuel n=Columnsort.sortColumn := by
  funext f
  exact (RecursiveColumnsort.localRun_correct q.height (height_pos q) fuel n f).eq_sortColumn

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : (swap q).condition) (fuel n : ℕ)
    (ha : Admissible q.height fuel n) (hd : Descriptors q fuel n)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+LocalSorter.space swap q hnormal fuel n≤limit) (hl : limit≤q.N^q.exponent) :
    Program q n source buffer limit Columnsort.sortColumn :=
  (LocalSorter.build swap q reader hnormal fuel n ha hd source buffer limit hs hw hl).val.changeFunction
    (operation_eq_sortColumn q fuel n)

theorem program_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : (swap q).condition) (fuel n : ℕ)
    (ha : Admissible q.height fuel n) (hd : Descriptors q fuel n)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+LocalSorter.space swap q hnormal fuel n≤limit) (hl : limit≤q.N^q.exponent) :
    (program swap q reader hnormal fuel n ha hd source buffer limit hs hw hl).charge≤
      LocalSorter.budget swap q fuel n := by
  unfold program
  rw [CommonRecordReindex.changeFunction_charge]
  exact (LocalSorter.build swap q reader hnormal fuel n ha hd source buffer limit hs hw hl).property

/-- Correct output, preservation, halt, transfer cost and RAM refer to one
actual execution, beginning with arbitrary workspace and arbitrary RAM
except for the initial program counter. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : (swap q).condition) (fuel n : ℕ)
    (ha : Admissible q.height fuel n) (hd : Descriptors q fuel n)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+LocalSorter.space swap q hnormal fuel n≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f)
    (hsize : LocalSorter.budget swap q fuel n≤q.N^q.exponent)
    (hpc : pc q s.ram=0) :
    let p := program swap q reader hnormal fuel n ha hd source buffer limit hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    Encoded q result.1.disk source (Columnsort.sortColumn f) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+recordBlocks q n≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧
    result.2≤LocalSorter.budget swap q fuel n ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  let p := program swap q reader hnormal fuel n ha hd source buffer limit hs hw hl
  have hc : p.charge≤LocalSorter.budget swap q fuel n :=
    program_charge_le swap q reader hnormal fuel n ha hd source buffer limit hs hw hl
  obtain ⟨hout,hframe,hhalt,hcost,hram⟩ :=
    CommonRecordProgram.complete q p s f hf (hc.trans hsize) hpc
  exact ⟨hout,hframe,hhalt,hcost.trans hc,hram⟩

/-- Public three-level local sorter. Leaf sizes and every intermediate
word descriptor are discharged from the local input range. -/
def localProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : (swap q).condition) (n : ℕ) (hn : n≤q.height^2) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+LocalSorter.space swap q hnormal 3 n≤limit) (hl : limit≤q.N^q.exponent) :
    Program q n source buffer limit Columnsort.sortColumn :=
  program swap q reader hnormal 3 n (CommonLocalAdmissible.three q.height n (height_pos q) hn)
    (CommonLocalDescriptors.of_height_squared q 3 n hn he) source buffer limit hs hw hl

theorem local_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : (swap q).condition) (n : ℕ) (hn : n≤q.height^2) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+LocalSorter.space swap q hnormal 3 n≤limit) (hl : limit≤q.N^q.exponent) :
    (localProgram swap q reader hnormal n hn he source buffer limit hs hw hl).charge≤
      LocalSorter.budget swap q 3 n :=
  program_charge_le swap q reader hnormal 3 n _ _ source buffer limit hs hw hl

theorem local_complete (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : (swap q).condition) (n : ℕ) (hn : n≤q.height^2) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+LocalSorter.space swap q hnormal 3 n≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f)
    (hsize : LocalSorter.budget swap q 3 n≤q.N^q.exponent)
    (hpc : pc q s.ram=0) :
    let p := localProgram swap q reader hnormal n hn he source buffer limit hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    Encoded q result.1.disk source (Columnsort.sortColumn f) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+recordBlocks q n≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧
    result.2≤LocalSorter.budget swap q 3 n ∧
    Fintype.card (ResidentIndex q)≤q.M :=
  complete swap q reader hnormal 3 n _ _ source buffer limit hs hw hl s f hf hsize hpc

end
end CodedSorting.LocalSorter.Machine

namespace CodedSorting.CommonLocalMachine
open CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonLocalRecursion CommonLocalAdmissible CommonPrunedParameters
open CommonLeafProgram (Machine)
noncomputable section
abbrev operation_eq_sortColumn := LocalSorter.Machine.operation_eq_sortColumn
abbrev program := LocalSorter.Machine.program frameworkLocalExchange
abbrev program_charge_le := LocalSorter.Machine.program_charge_le frameworkLocalExchange
abbrev complete := LocalSorter.Machine.complete frameworkLocalExchange
def localProgram := LocalSorter.Machine.localProgram frameworkLocalExchange
theorem local_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (n : ℕ) (hn : n≤q.height^2) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+space q hnormal 3 n≤limit) (hl : limit≤q.N^q.exponent) :
    (localProgram q reader hnormal n hn he source buffer limit hs hw hl).charge≤
      CommonLocalBudget.budget q 3 n :=
  LocalSorter.Machine.local_charge_le frameworkLocalExchange q reader hnormal n hn he source buffer limit hs hw hl
theorem local_complete (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (n : ℕ) (hn : n≤q.height^2) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+space q hnormal 3 n≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f)
    (hsize : CommonLocalBudget.budget q 3 n≤q.N^q.exponent)
    (hpc : pc q s.ram=0) :
    let p := localProgram q reader hnormal n hn he source buffer limit hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    Encoded q result.1.disk source (Columnsort.sortColumn f) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+recordBlocks q n≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧
    result.2≤CommonLocalBudget.budget q 3 n ∧
    Fintype.card (ResidentIndex q)≤q.M :=
  LocalSorter.Machine.local_complete frameworkLocalExchange q reader hnormal n hn he source buffer limit hs hw hl s f hf hsize hpc
end
end CodedSorting.CommonLocalMachine
end Program

section Improved
/-! The complete three-level local machine with the improved I/O bound.
There is no supplied sorting oracle or exchange-rate contract: both the
program and its charge are constructed from the public machine parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace CodedSorting.CommonLocalImproved
open CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonLocalRecursion CommonPrunedParameters RecursiveExchange
open CommonLeafProgram (Machine)
noncomputable section
attribute [local irreducible] CommonLocalMachine.localProgram
  ControlledNormalization.runLogical Parameters.W Parameters.m radix

def normalized (q : Configuration)
    (hthreshold : PhysicalLeafParameters.minimumRatio radix 1 Parameters.W≤q.inventory.ratio) :
    Normalized q :=
  CommonSortingExchangeRate.normal_of_height q
    (CommonSortingExchangeRate.normal_height_of_inventory q hthreshold)

/-- The same run sorts all records, preserves unrelated disk regions,
halts, satisfies the logarithmic improved charge, and uses the accounted
RAM. Source separation, workspace capacity and total PC capacity remain
explicit; global MSD and the final physical normalization are separate. -/
theorem local_complete_improved (q : Configuration) (reader : Fin q.inventory.readers)
    (hthreshold : PhysicalLeafParameters.minimumRatio radix 1 Parameters.W≤q.inventory.ratio)
    (n : ℕ) (hn : 0<n) (hlocal : n≤q.height^2) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+space q (normalized q hthreshold) 3 n≤limit)
    (hl : limit≤q.N^q.exponent)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f)
    (hsize : CommonLocalBudget.budget q 3 n≤q.N^q.exponent)
    (hpc : pc q s.ram=0) :
    let p := CommonLocalMachine.localProgram q reader (normalized q hthreshold)
      n hlocal he source buffer limit hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    Encoded q result.1.disk source (Columnsort.sortColumn f) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+recordBlocks q n≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧
    (result.2 : ℝ)≤CommonLocalBudgetRate.boundConstant*(1+(n : ℝ)/q.block)*
      (1+(Real.log (n : ℝ)/Real.log ((q.height : ℝ)/q.block))^
        (1-(Parameters.epsilon : ℝ))) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hout,hframe,hhalt,hcost,hram⟩ := CommonLocalMachine.local_complete q reader
    (normalized q hthreshold) n hlocal he source buffer limit hs hw hl s f hf hsize hpc
  refine ⟨hout,hframe,hhalt,?_,hram⟩
  have hr := CommonLocalBudgetRate.improved_bound q n hn hlocal
    (CommonSortingExchangeRate.normal_height_of_inventory q hthreshold)
  exact (Nat.cast_le.mpr hcost).trans hr

end
end CodedSorting.CommonLocalImproved
end Improved
