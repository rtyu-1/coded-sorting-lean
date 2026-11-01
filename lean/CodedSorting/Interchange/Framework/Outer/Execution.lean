import CodedSorting.Interchange.Framework.Memory.Reflection

section Streams
/-! Concrete two-colour stream data for the outer subtraction stage of the
coded exchange. These are precisely the passes of the existing complete
file interpreter, with its unchanged physical address layout. No input
payload appears in any permutation, colour or schedule parameter.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
namespace CodedSorting.CommonOuterStreams
open Address RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open CommonAddressLayout CoordinateScans ScanProgram OuterExchangeProgram CodedSimulation
noncomputable section

private def castPermutation {V U : ℕ} (h : V=U) (e : Equiv.Perm (Fin V)) :
    Equiv.Perm (Fin U) := (finCongr h).symm.trans (e.trans (finCongr h))

private theorem cast_increasing {V U K : ℕ} (h : V=U)
    (e : Equiv.Perm (Fin V)) (key : Fin V → Fin K)
    (hi : ∀ x y,x<y → key x=key y → e x<e y) :
    ∀ x y,x<y → key ((finCongr h).symm x)=key ((finCongr h).symm y) →
      castPermutation h e x<castPermutation h e y := by
  subst U
  exact hi

private theorem cast_streams {V U K : ℕ} (h : V=U)
    (e : Equiv.Perm (Fin V)) (key : Fin V → Fin K)
    (hi : ∀ x y,x<y → key x=key y → e x<e y) :
    BlockDigitMove.castPass h (.streams K e key hi)=
      .streams K (castPermutation h e) (fun x => key ((finCongr h).symm x))
        (cast_increasing h e key hi) := by
  subst U
  rfl

/-- The ordinary low-field addition, under the actual whole-vector layout. -/
def addition (f P G S : ℕ) (i : Index) : Equiv.Perm (Fin (longVolume f P G S)) :=
  castPermutation (scalarVolume f P G S i)
    (globalLowAdd (P:=ChildPrefix P (radix^f) i) (Q:=radix^f)
      (G:=ChildGap G (radix^f) i i) (S:=ChildSuffix S (radix^f) i))

def additionColour (f P G S : ℕ) (i : Index) : Fin (longVolume f P G S) → Fin 2 :=
  fun x => globalLowAddKey ((finCongr (scalarVolume f P G S i)).symm x)

theorem addition_increasing (f P G S : ℕ) (i : Index) :
    ∀ x y,x<y → additionColour f P G S i x=additionColour f P G S i y →
      addition f P G S i x<addition f P G S i y := by
  apply cast_increasing (scalarVolume f P G S i)
  exact TriangularStreams.global_increasing_streams
    (fun p => AffineStreams.additionEquiv (lowOffset p))
    (fun p => SequentialArithmetic.additionRun (lowOffset p))
    (fun p x y hxy hr => SequentialArithmetic.addition_increasing_in_run (lowOffset p) x y hxy hr)

/-- The first outer stage subtracts the corresponding high coordinate. -/
def subtraction (f P G S : ℕ) (i : Index) : Equiv.Perm (Fin (longVolume f P G S)) :=
  (addition f P G S i).symm

def subtractionColour (f P G S : ℕ) (i : Index) : Fin (longVolume f P G S) → Fin 2 :=
  fun x => additionColour f P G S i (subtraction f P G S i x)

theorem subtraction_increasing (f P G S : ℕ) (i : Index) :
    ∀ x y,x<y → subtractionColour f P G S i x=subtractionColour f P G S i y →
      subtraction f P G S i x<subtraction f P G S i y :=
  AffineStreams.inverse_increasing_streams _ _ (addition_increasing f P G S i)

def pass (f P G S : ℕ) (i : Index) : Pass (longVolume f P G S) :=
  .streams 2 (subtraction f P G S i) (subtractionColour f P G S i)
    (subtraction_increasing f P G S i)

/-- The concrete colour/permutation pair is the interpreter's exact pass,
not merely another transformation with the same claimed cost. -/
theorem subtractOne_eq (f P G S : ℕ) (i : Index) :
    subtractOne f P G S i=[pass f P G S i] := by
  unfold subtractOne BlockDigitMove.inverseProgram addOne BlockDigitMove.castProgram
    ScalarCoordinateProgram.before
  simp only [List.map_cons,List.map_nil,List.reverse_cons,List.reverse_nil,List.nil_append]
  rw [cast_streams]
  rfl

theorem subtraction_encoded (f P G S : ℕ) (i : Index) (a : Addr f P G S) :
    subtraction f P G S i (commonLayout f P G S a)=
      commonLayout f P G S (lowStep (fun h d => d-h) i a) := by
  have h := subtractOne_destination f P G S i a
  rw [subtractOne_eq] at h
  exact h

/-- The complete before stage is exactly one two-colour pass per matrix
coordinate, in the pre-existing coordinate order. -/
theorem beforeProgram_eq (f P G S : ℕ) :
    OuterExchangeProgram.beforeProgram f P G S=coordinates.map (pass f P G S) := by
  have hs : subtractOne f P G S=(fun i => [pass f P G S i]) :=
    funext (subtractOne_eq f P G S)
  rw [OuterExchangeProgram.beforeProgram,hs]
  exact List.map_eq_flatMap.symm

theorem beforeProgram_length (f P G S : ℕ) :
    (OuterExchangeProgram.beforeProgram f P G S).length=Parameters.m := by
  rw [beforeProgram_eq,List.length_map,coordinates_length]

/-- The generated stream list has the original full-vector effect. -/
theorem before_encoded (f P G S : ℕ) (a : Addr f P G S) :
    destination (coordinates.map (pass f P G S)) (commonLayout f P G S a)=
      commonLayout f P G S (mapPairEquiv lowerSubtractEquiv a) := by
  rw [←beforeProgram_eq]
  exact before_destination f P G S a

end
end CodedSorting.CommonOuterStreams
end Streams

section Execution
/-! The complete outer subtraction is one actual common-machine program.
Each coordinate pass writes into the other of two disjoint disk regions;
that result is the next pass's input. Only public dimensions and addresses
occur in the program text. All passes use the existing reader buffer and
transfer window, and one finite program counter controls their concatenation.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonOuterExecution
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge ScanProgram
open OuterExchangeProgram CommonOuterStreams Address CodedSimulation
noncomputable section

/-- A single physical coordinate-subtraction pass. -/
def coordinateCode (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (i : Index) (source target : ℕ) : List (Instruction q) :=
  CommonPermutationScan.program q reader (subtraction f P G S i)
    (subtractionColour f P G S i) source target

/-- The two allocated regions alternate their roles after every pass. -/
def finalBase : List Index → ℕ → ℕ → ℕ
  | [],source,_ => source
  | _::is,source,target => finalBase is target source

theorem finalBase_length (is : List Index) (source target : ℕ) :
    finalBase is source target=(if is.length%2=0 then source else target) := by
  induction is generalizing source target with
  | nil => simp [finalBase]
  | cons i is ih =>
    rw [finalBase,ih,List.length_cons]
    have hm : is.length%2<2 := Nat.mod_lt _ (by omega)
    by_cases h : is.length%2=0
    · have hn : (is.length+1)%2≠0 := by omega
      simp only [if_pos h,if_neg hn]
    · have hn : (is.length+1)%2=0 := by omega
      simp only [if_neg h,if_pos hn]

/-- There are an even number of vector coordinates, so the complete
before stage leaves its result in the original source region. -/
theorem finalBase_coordinates (source target : ℕ) :
    finalBase coordinates source target=source := by
  rw [finalBase_length,coordinates_length,Parameters.m_value]
  norm_num

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) : List Index → ℕ → ℕ → List (Instruction q)
  | [],_,_ => []
  | i::is,source,target => coordinateCode q reader f P G S i source target ++
      code q reader f P G S is target source

theorem coordinate_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (i : Index) (source target : ℕ) :
    (coordinateCode q reader f P G S i source target).length≤
      12*count q (longVolume f P G S) := by
  exact CommonPermutationScan.program_length q reader _ _ source target
    (subtraction_increasing f P G S i)

theorem coordinate_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (i : Index) (source target : ℕ) :
    ∀ ins∈coordinateCode q reader f P G S i source target,RespectsPC q ins :=
  CommonPermutationScan.program_safe q reader _ _ source target

theorem length_le (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (is : List Index) (source target : ℕ) :
    (code q reader f P G S is source target).length≤
      12*is.length*count q (longVolume f P G S) := by
  induction is generalizing source target with
  | nil => simp [code]
  | cons i is ih =>
    rw [code,List.length_append,List.length_cons]
    have h := coordinate_length q reader f P G S i source target
    have ht := ih target source
    nlinarith

theorem cost_eq_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (is : List Index) (source target : ℕ) :
    cost q (code q reader f P G S is source target)=
      (code q reader f P G S is source target).length := by
  induction is generalizing source target with
  | nil => rfl
  | cons i is ih =>
    rw [code,CommonPermutationPairs.cost_append,List.length_append,ih]
    congr 1
    unfold coordinateCode CommonPermutationScan.program
    rw [CommonPermutationPairs.code_cost,CommonPermutationPairs.code_length]

theorem safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (is : List Index) (source target : ℕ) :
    ∀ ins∈code q reader f P G S is source target,RespectsPC q ins := by
  induction is generalizing source target with
  | nil => simp [code]
  | cons i is ih =>
    intro ins hi
    rcases List.mem_append.mp hi with hi|hi
    · exact coordinate_safe q reader f P G S i source target ins hi
    · exact ih target source ins hi

/-- Input bits are taken from the previous pass's actual output disk. -/
theorem raw_correct (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (is : List Index) (source target : ℕ) (s : Machine q)
    (hs : source+count q (longVolume f P G S)≤q.N^q.exponent)
    (ht : target+count q (longVolume f P G S)≤q.N^q.exponent)
    (hsep : source+count q (longVolume f P G S)≤target ∨
      target+count q (longVolume f P G S)≤source)
    (x : Fin (longVolume f P G S)) :
    readBit q (executeRaw q (code q reader f P G S is source target) s).1.disk
        (finalBase is source target) (destination (is.map (pass f P G S)) x).val=
      readBit q s.disk source x.val := by
  induction is generalizing source target s x with
  | nil => rfl
  | cons i is ih =>
    rw [code,CommonPermutationPairs.raw_append]
    change readBit q _ (finalBase is target source)
      (destination (is.map (pass f P G S)) (subtraction f P G S i x)).val=_
    rw [ih target source _ ht hs hsep.symm]
    have h := (CommonPermutationScan.raw_correct q reader (subtraction f P G S i)
      (subtractionColour f P G S i) source target hs ht hsep s).1 (subtraction f P G S i x)
    simpa only [Equiv.symm_apply_apply] using h

/-- Both scratch regions may change; all unrelated disk files are preserved. -/
theorem raw_outside (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (is : List Index) (source target : ℕ) (s : Machine q)
    (hs : source+count q (longVolume f P G S)≤q.N^q.exponent)
    (ht : target+count q (longVolume f P G S)≤q.N^q.exponent)
    (hsep : source+count q (longVolume f P G S)≤target ∨
      target+count q (longVolume f P G S)≤source)
    (a : Fin (q.N^q.exponent))
    (has : a.val<source ∨ source+count q (longVolume f P G S)≤a.val)
    (hat : a.val<target ∨ target+count q (longVolume f P G S)≤a.val) :
    (executeRaw q (code q reader f P G S is source target) s).1.disk a=s.disk a := by
  induction is generalizing source target s with
  | nil => rfl
  | cons i is ih =>
    rw [code,CommonPermutationPairs.raw_append,ih target source _ ht hs hsep.symm hat has]
    exact (CommonPermutationScan.raw_correct q reader (subtraction f P G S i)
      (subtractionColour f P G S i) source target hs ht hsep s).2 a hat

/-- Complete, halted, same-run execution of the entire before stage, with
its original vector-coordinate meaning and charged block transfers. -/
theorem before_complete (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source target : ℕ) (s : Machine q)
    (hs : source+count q (longVolume f P G S)≤q.N^q.exponent)
    (ht : target+count q (longVolume f P G S)≤q.N^q.exponent)
    (hsep : source+count q (longVolume f P G S)≤target ∨
      target+count q (longVolume f P G S)≤source)
    (hsize : 12*Parameters.m*count q (longVolume f P G S)≤q.N^q.exponent)
    (hpc : pc q s.ram=0) :
    let program := code q reader f P G S coordinates source target
    let result := ControlledNormalization.runLogical (policy q program) program.length s
    (∀ a : Addr f P G S,
      readBit q result.1.disk source
        (commonLayout f P G S (mapPairEquiv lowerSubtractEquiv a)).val=
      readBit q s.disk source (commonLayout f P G S a).val) ∧
    policy q program result.1.ram=none ∧
    result.2≤12*Parameters.m*count q (longVolume f P G S) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  dsimp only
  have hl := length_le q reader f P G S coordinates source target
  rw [coordinates_length] at hl
  obtain ⟨hd,hh,hc,hm⟩ := run_code_disk q _ (hl.trans hsize)
    (safe q reader f P G S coordinates source target) s hpc
  refine ⟨?_,hh,?_,hm⟩
  · intro a
    rw [hd]
    have h := raw_correct q reader f P G S coordinates source target s hs ht hsep
      (commonLayout f P G S a)
    rw [CommonOuterStreams.before_encoded,finalBase_coordinates] at h
    exact h
  · rw [hc,cost_eq_length]
    exact hl

end
end CodedSorting.CommonOuterExecution
end Execution
