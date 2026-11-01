import CodedSorting.Interchange.Framework.Memory.Reflection

section Semantics
/-! Pointwise glue for the lowest nonleaf's physical layout. These equalities
identify literal packed array positions with the existing source, sink and
whole-exchange semantics. They create no files and assert no machine run.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonOneLevelSemantics
open Address RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open PhysicalRolePartition Circuit CircuitProgram ProgramNetwork CodedSimulation
noncomputable section

abbrev Local (f R G S : ℕ) :=
  LongAddress (Prefix:=Fin R) (Gap:=Fin G) (Suffix:=Fin S) f
abbrev Parent (f R G S : ℕ) := Local f (R*Parameters.W) G S

/-- A role's live bits occupy consecutive positions after the role transpose. -/
def groupedIndex (f R G S : ℕ) (r : Reg) (i : Fin (longVolume f R G S)) :
    Fin (Parameters.W*(R*segmentVolume f G S)) :=
  finProdFinEquiv (roleEnumeration r,finCongr (local_volume f R G S) i)

theorem groupedIndex_val (f R G S : ℕ) (r : Reg) (i : Fin (longVolume f R G S)) :
    (groupedIndex f R G S r i).val=(roleEnumeration r).val*longVolume f R G S+i.val := by
  simp only [groupedIndex,finProdFinEquiv_apply_val,finCongr_apply_coe]
  have h := congrArg (fun n => (roleEnumeration r).val*n+i.val) (local_volume f R G S)
  calc
    _ = (roleEnumeration r).val*(R*segmentVolume f G S)+i.val := by ring
    _ = _ := h.symm

/-- The original parent position which supplies this role-file bit. -/
def scatterIndex (f R G S : ℕ) (r : Reg) (i : Fin (longVolume f R G S)) :
    Fin (longVolume f (R*Parameters.W) G S) :=
  (finCongr (parent_volume f R G S)).symm
    (rolePermutation.symm (groupedIndex f R G S r i))

theorem scatterIndex_at (f R G S : ℕ) (r : Reg) (a : Local f R G S) :
    scatterIndex f R G S r (commonLayout f R G S a)=
      commonLayout f (R*Parameters.W) G S ((splitPrefix f).symm (r,a)) := by
  have h := splitPrefix_same_address f R G S ((splitPrefix f).symm (r,a))
  simp only [Equiv.apply_symm_apply] at h
  have hi := congrArg (fun j => (finCongr (parent_volume f R G S)).symm
    (rolePermutation.symm j)) h
  simpa only [Equiv.symm_apply_apply] using hi.symm

/-- Numeric source position for any local bit index, with no implicit repacking. -/
theorem scatterIndex_linear (f R G S : ℕ) (r : Reg) (i : Fin (longVolume f R G S)) :
    scatterIndex f R G S r i=
      commonLayout f (R*Parameters.W) G S
        ((splitPrefix f).symm (r,(commonLayout f R G S).symm i)) := by
  simpa only [Equiv.apply_symm_apply] using
    scatterIndex_at f R G S r ((commonLayout f R G S).symm i)

/-- A direct pointwise form of the role splitter's array specification. -/
def scattered (f R G S : ℕ)
    (F : Fin (longVolume f (R*Parameters.W) G S)→Bit) (r : Reg)
    (i : Fin (longVolume f R G S)) : Bit := F (scatterIndex f R G S r i)

theorem scattered_at (f R G S : ℕ) (F : Parent f R G S→Bit)
    (r : Reg) (a : Local f R G S) :
    scattered f R G S (F ∘ (commonLayout f (R*Parameters.W) G S).symm)
      r (commonLayout f R G S a)=splitInput f F r a := by
  simp only [scattered,Function.comp_apply,scatterIndex_at,Equiv.symm_apply_apply]
  rfl

/-- The collector reads one packed role file at a time in roleEnumeration
order. The surrounding inverse transpose restores the parent layout. -/
def collected (f R G S : ℕ)
    (output : Reg→Fin (longVolume f R G S)→Bit)
    (i : Fin (longVolume f (R*Parameters.W) G S)) : Bit :=
  let grouped := rolePermutation (finCongr (parent_volume f R G S) i)
  let pair := finProdFinEquiv.symm grouped
  output (roleEnumeration.symm pair.1) ((finCongr (local_volume f R G S)).symm pair.2)

theorem collected_at (f R G S : ℕ) (output : Reg→Local f R G S→Bit)
    (a : Parent f R G S) :
    collected f R G S (fun r => output r ∘ (commonLayout f R G S).symm)
      (commonLayout f (R*Parameters.W) G S a)=gatherOutput f output a := by
  simp only [collected,splitPrefix_same_address,Equiv.symm_apply_apply,Function.comp_apply]
  rfl

/-- The output role r is read from the designated crossed sink, rather than
from an unchanged register number or an arbitrary last-stage wire. -/
def sinkValues (f R G S : ℕ) (input : Reg→Local f R G S→Bit)
    (r : Reg) (i : Fin (longVolume f R G S)) : Bit :=
  executePhysical f input (sinkWire (globalProgram Parameters.d) (globalSwap r))
    ((commonLayout f R G S).symm i)

theorem sinkValues_at (f R G S : ℕ) (input : Reg→Local f R G S→Bit)
    (r : Reg) (a : Local f R G S) :
    sinkValues f R G S input r (commonLayout f R G S a)=
      transport (matrixLocation (1 : Matrix Index Index (Scalar f))) (input r) a := by
  simp only [sinkValues,Equiv.symm_apply_apply]
  exact congrFun (physicalOutput_correct f input r) a

theorem collected_sinks (f R G S : ℕ) (F : Parent f R G S→Bit)
    (a : Parent f R G S) :
    collected f R G S (sinkValues f R G S (splitInput f F))
      (commonLayout f (R*Parameters.W) G S a)=
      transport (matrixLocation (1 : Matrix Index Index (Scalar f))) F a := by
  have he : sinkValues f R G S (splitInput f F)=
      fun r => transport (matrixLocation (1 : Matrix Index Index (Scalar f)))
        (splitInput f F r) ∘ (commonLayout f R G S).symm := by
    funext r i
    have h := sinkValues_at f R G S (splitInput f F) r ((commonLayout f R G S).symm i)
    simpa only [Equiv.apply_symm_apply] using h
  rw [he,collected_at,gather_transported_split]

/-- Literal physical-network semantics between the two outer transforms. -/
def physicalFull (f R G S : ℕ) (F : Parent f R G S→Bit) : Parent f R G S→Bit :=
  transport (mapPairEquiv lowerReflectEquiv)
    (fun a => collected f R G S
      (sinkValues f R G S (splitInput f (transport (mapPairEquiv lowerSubtractEquiv) F)))
      (commonLayout f (R*Parameters.W) G S a))

/-- The actual source splitting, crossed sink ordering and final collection
produce precisely the complete address exchange. -/
theorem physical_full_correct (f R G S : ℕ) (F : Parent f R G S→Bit) :
    physicalFull f R G S F=transport exchangeEquiv F := by
  unfold physicalFull
  simp_rw [collected_sinks]
  rw [matrixLocation_one,transport_comp,transport_comp,full_three_step_exchange]

/-- Pointwise endpoint for composing machine stages at literal array addresses. -/
theorem physical_full_linear (f R G S : ℕ)
    (F : Fin (longVolume f (R*Parameters.W) G S)→Bit)
    (i : Fin (longVolume f (R*Parameters.W) G S)) :
    physicalFull f R G S (F ∘ (commonLayout f (R*Parameters.W) G S))
      ((commonLayout f (R*Parameters.W) G S).symm i)=
    F (commonLayout f (R*Parameters.W) G S
      (exchangeEquiv.symm ((commonLayout f (R*Parameters.W) G S).symm i))) := by
  rw [physical_full_correct]
  rfl

end
end CodedSorting.CommonOneLevelSemantics
end Semantics

section Roles
/-! The role transpose and its inverse on one actual finite disk. Their
pointwise specifications use live role-file offsets, without padded words.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonOneLevelRoles
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonOneLevelSemantics PhysicalRolePartition
open Address RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge Circuit
noncomputable section

private def castPermutation {V U : ℕ} (h : V=U) (e : Equiv.Perm (Fin U)) :
    Equiv.Perm (Fin V) := (finCongr h).trans (e.trans (finCongr h).symm)

private theorem cast_increasing {V U K : ℕ} (h : V=U) (e : Equiv.Perm (Fin U))
    (key : Fin U→Fin K)
    (hi : ∀ x y,x<y → key x=key y → e x<e y) :
    ∀ x y,x<y → key (finCongr h x)=key (finCongr h y) →
      castPermutation h e x<castPermutation h e y := by
  subst U
  exact hi

private theorem cast_inverse_increasing {V U K : ℕ} (h : V=U) (e : Equiv.Perm (Fin U))
    (key : Fin U→Fin K)
    (hi : ∀ x y,x<y → key x=key y → e.symm x<e.symm y) :
    ∀ x y,x<y → key (finCongr h x)=key (finCongr h y) →
      (castPermutation h e).symm x<(castPermutation h e).symm y := by
  subst U
  exact hi

def transpose (f R G S : ℕ) : Equiv.Perm (Fin (longVolume f (R*Parameters.W) G S)) :=
  castPermutation (parent_volume f R G S)
    (rolePermutation (R:=R) (K:=Parameters.W) (C:=segmentVolume f G S))

def sourceColour (f R G S : ℕ) (x : Fin (longVolume f (R*Parameters.W) G S)) : Fin Parameters.W :=
  sourceKey (R:=R) (K:=Parameters.W) (C:=segmentVolume f G S)
    (finCongr (parent_volume f R G S) x)
def targetColour (f R G S : ℕ) (x : Fin (longVolume f (R*Parameters.W) G S)) : Fin Parameters.W :=
  targetKey (R:=R) (K:=Parameters.W) (C:=segmentVolume f G S)
    (finCongr (parent_volume f R G S) x)

theorem transpose_increasing (f R G S : ℕ) :
    ∀ x y,x<y → sourceColour f R G S x=sourceColour f R G S y →
      transpose f R G S x<transpose f R G S y :=
  cast_increasing (parent_volume f R G S)
    (rolePermutation (R:=R) (K:=Parameters.W) (C:=segmentVolume f G S))
    (sourceKey (R:=R) (K:=Parameters.W) (C:=segmentVolume f G S))
    (role_increasing (R:=R) (K:=Parameters.W) (C:=segmentVolume f G S))

theorem inverse_increasing (f R G S : ℕ) :
    ∀ x y,x<y → targetColour f R G S x=targetColour f R G S y →
      (transpose f R G S).symm x<(transpose f R G S).symm y :=
  cast_inverse_increasing (parent_volume f R G S)
    (rolePermutation (R:=R) (K:=Parameters.W) (C:=segmentVolume f G S))
    (targetKey (R:=R) (K:=Parameters.W) (C:=segmentVolume f G S))
    (PhysicalRolePartition.inverse_increasing (R:=R) (K:=Parameters.W) (C:=segmentVolume f G S))

def forwardCode (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source target : ℕ) : List (Instruction q) :=
  CommonPermutationScan.program q reader (transpose f R G S) (sourceColour f R G S) source target

def inverseCode (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source target : ℕ) : List (Instruction q) :=
  CommonPermutationScan.program q reader (transpose f R G S).symm (targetColour f R G S) source target

theorem forward_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source target : ℕ) (s : Machine q)
    (hs : source+count q (longVolume f (R*Parameters.W) G S)≤q.N^q.exponent)
    (ht : target+count q (longVolume f (R*Parameters.W) G S)≤q.N^q.exponent)
    (hsep : source+count q (longVolume f (R*Parameters.W) G S)≤target ∨
      target+count q (longVolume f (R*Parameters.W) G S)≤source)
    (r : Reg) (a : Local f R G S) :
    readBit q (executeRaw q (forwardCode q reader f R G S source target) s).1.disk
      target ((roleEnumeration r).val*longVolume f R G S+(commonLayout f R G S a).val)=
    readBit q s.disk source
      (commonLayout f (R*Parameters.W) G S ((splitPrefix f).symm (r,a))).val := by
  unfold forwardCode
  let j := (finCongr (parent_volume f R G S)).symm
    (groupedIndex f R G S r (commonLayout f R G S a))
  have hv : j.val=(roleEnumeration r).val*longVolume f R G S+(commonLayout f R G S a).val :=
    groupedIndex_val f R G S r (commonLayout f R G S a)
  have he : (transpose f R G S).symm j=
      commonLayout f (R*Parameters.W) G S ((splitPrefix f).symm (r,a)) := by
    change scatterIndex f R G S r (commonLayout f R G S a)=_
    exact scatterIndex_at f R G S r a
  have h := (CommonPermutationScan.raw_correct q reader (transpose f R G S)
    (sourceColour f R G S) source target hs ht hsep s).1 j
  rw [hv,he] at h
  exact h

theorem inverse_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source target : ℕ) (s : Machine q)
    (hs : source+count q (longVolume f (R*Parameters.W) G S)≤q.N^q.exponent)
    (ht : target+count q (longVolume f (R*Parameters.W) G S)≤q.N^q.exponent)
    (hsep : source+count q (longVolume f (R*Parameters.W) G S)≤target ∨
      target+count q (longVolume f (R*Parameters.W) G S)≤source)
    (output : Reg→Local f R G S→Bit)
    (hinput : ∀ r a,readBit q s.disk source
      ((roleEnumeration r).val*longVolume f R G S+(commonLayout f R G S a).val)=output r a)
    (a : Parent f R G S) :
    readBit q (executeRaw q (inverseCode q reader f R G S source target) s).1.disk
      target (commonLayout f (R*Parameters.W) G S a).val=gatherOutput f output a := by
  unfold inverseCode gatherOutput
  have h := (CommonPermutationScan.raw_correct q reader (transpose f R G S).symm
    (targetColour f R G S) source target hs ht hsep s).1
    (commonLayout f (R*Parameters.W) G S a)
  have hv : (transpose f R G S (commonLayout f (R*Parameters.W) G S a)).val=
      (roleEnumeration ((splitPrefix f) a).1).val*longVolume f R G S+
        (commonLayout f R G S ((splitPrefix f) a).2).val := by
    change (rolePermutation (finCongr (parent_volume f R G S)
      (commonLayout f (R*Parameters.W) G S a))).val=_
    rw [splitPrefix_same_address]
    exact groupedIndex_val f R G S _ _
  rw [Equiv.symm_symm,hv,hinput] at h
  exact h

theorem forward_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source target : ℕ) : ∀ i∈forwardCode q reader f R G S source target,RespectsPC q i :=
  CommonPermutationScan.program_safe q reader _ _ source target

theorem inverse_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source target : ℕ) : ∀ i∈inverseCode q reader f R G S source target,RespectsPC q i :=
  CommonPermutationScan.program_safe q reader _ _ source target

theorem forward_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source target : ℕ) :
    (forwardCode q reader f R G S source target).length≤
      6*Parameters.W*count q (longVolume f (R*Parameters.W) G S) :=
  CommonPermutationScan.program_length q reader _ _ source target (transpose_increasing f R G S)
theorem inverse_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source target : ℕ) :
    (inverseCode q reader f R G S source target).length≤
      6*Parameters.W*count q (longVolume f (R*Parameters.W) G S) :=
  CommonPermutationScan.program_length q reader _ _ source target (inverse_increasing f R G S)
theorem forward_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source target : ℕ) :
    cost q (forwardCode q reader f R G S source target)≤
      6*Parameters.W*count q (longVolume f (R*Parameters.W) G S) :=
  CommonPermutationScan.program_cost q reader _ _ source target (transpose_increasing f R G S)
theorem inverse_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source target : ℕ) :
    cost q (inverseCode q reader f R G S source target)≤
      6*Parameters.W*count q (longVolume f (R*Parameters.W) G S) :=
  CommonPermutationScan.program_cost q reader _ _ source target (inverse_increasing f R G S)

end
end CodedSorting.CommonOneLevelRoles
end Roles
