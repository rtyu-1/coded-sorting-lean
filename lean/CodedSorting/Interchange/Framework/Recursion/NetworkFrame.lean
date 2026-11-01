import CodedSorting.Interchange.Framework.Recursion.Network

section NetworkRun
/-! Chronological network execution with recursively implemented edge maps. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace CodedSorting.CommonRecursiveNetwork
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Disk Machine)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open PhysicalRecursiveExchange CodedSimulation Address Circuit CircuitProgram ProgramNetwork
open CommonNetworkInputs (ports)
open CommonResidentNetwork
noncomputable section

/-- Every file lies strictly before the reusable recursive workspace. -/
theorem bit_outside_child (q : Configuration) (f P G S : ℕ) (p : Layout q f P G S)
    (file : CommonResidentNetwork.File) (i : Fin (longVolume f P G S)) :
    (CommonColumnSplit.address q (base p.workspace p.stride file)
      (i.val/CommonPermutationPairs.width q)).val<p.childBase := by
  have hi := CommonPermutationPairs.bit_block_lt q i
  have hc := p.count_le_stride
  have hf := base_fits q p.workspace p.stride p.network_fits file
  have hslot := slot_lt file
  have hmul := Nat.mul_le_mul_right p.stride (Nat.succ_le_of_lt hslot)
  rw [CommonColumnSplit.address_val q _ _ (by omega)]
  have ha : base p.workspace p.stride file+p.stride≤p.workspace+fileCount*p.stride := by
    dsimp only [base]; nlinarith
  exact (by omega : base p.workspace p.stride file+i.val/CommonPermutationPairs.width q<
    p.workspace+fileCount*p.stride).trans_le p.network_le_child

theorem prefix_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p)
    (n : ℕ) (hn : n≤edgeCount) (s : Machine q) (input : Inputs f P G S)
    (hinput : InputView q f P G S p.workspace p.stride s.disk input) :
    let result := executeRaw q (prefixCode q reader f P G S p ep n hn) s
    InputView q f P G S p.workspace p.stride result.1.disk input ∧
    EdgeView q f P G S p.workspace p.stride n result.1.disk input ∧
    (∀ a : Fin (q.N^q.exponent),a.val<p.workspace ∨ p.childLimit≤a.val →
      result.1.disk a=s.disk a) := by
  induction n with
  | zero => exact ⟨hinput,fun _ h => (Nat.not_lt_zero _ h).elim,fun _ _ => rfl⟩
  | succ n ih =>
    let e : Edge := edgeEnumeration.symm ⟨n,by omega⟩
    have he : (edgeEnumeration e).val=n := by simp only [e,Equiv.apply_symm_apply]
    let mid := (executeRaw q (prefixCode q reader f P G S p ep n (by omega)) s).1
    obtain ⟨hmi,hme,hmo⟩ := ih (by omega)
    have hprev : EdgeView q f P G S p.workspace p.stride (edgeEnumeration e).val mid.disk input := by
      rw [he]; exact hme
    obtain ⟨hout,hframe⟩ := edge_raw q reader f P G S p ep e mid input hmi hprev
    let final := (executeRaw q (edgeCode q reader f P G S p ep e) mid).1
    have hkeep : ∀ other : CommonResidentNetwork.File,other≠.inr (.inr ()) → other≠.inr (.inl e) →
        ∀ i : Fin (longVolume f P G S),
        CommonPermutationPairs.readBit q final.disk (base p.workspace p.stride other) i.val=
          CommonPermutationPairs.readBit q mid.disk (base p.workspace p.stride other) i.val := by
      intro other hs he' i
      unfold CommonPermutationPairs.readBit
      rw [hframe]
      · exact bit_outside_file q _ p.workspace p.stride p.count_le_stride p.network_fits other _ hs i
      · exact bit_outside_file q _ p.workspace p.stride p.count_le_stride p.network_fits other _ he' i
      · exact Or.inl (bit_outside_child q f P G S p other i)
    dsimp only
    have hrun : (executeRaw q (prefixCode q reader f P G S p ep (n+1) hn) s).1=final := by
      exact CommonPermutationPairs.raw_append q
        (prefixCode q reader f P G S p ep n (by omega))
        (edgeCode q reader f P G S p ep e) s
    rw [hrun]
    refine ⟨?_,?_,?_⟩
    · intro r a
      exact (hkeep (.inl r) (by simp) (by simp) (commonLayout f P G S a)).trans (hmi r a)
    · intro old hold a
      by_cases hold' : old=e
      · subst old; exact hout a
      · have henum : (edgeEnumeration old).val≠n := by
          intro h
          apply hold'
          apply edgeEnumeration.injective
          apply Fin.ext
          exact h.trans he.symm
        have hp : (edgeEnumeration old).val<n := by omega
        exact (hkeep (.inr (.inl old)) (by simp) (by simpa using hold')
          (commonLayout f P G S a)).trans (hme old hp a)
    · intro a ha
      have harena : a.val<p.workspace ∨ p.workspace+fileCount*p.stride≤a.val := by
        rcases ha with h|h
        · exact Or.inl h
        · exact Or.inr (p.network_le_child.trans (p.child_le_limit.trans h))
      have hchild : a.val<p.childBase ∨ p.childLimit≤a.val := by
        rcases ha with h|h
        · left; exact h.trans_le ((Nat.le_add_right _ _).trans p.network_le_child)
        · exact Or.inr h
      exact (hframe a (outside_workspace p.workspace p.stride a.val harena _)
        (outside_workspace p.workspace p.stride a.val harena _) hchild).trans (hmo a ha)

/-- The concrete XOR scans and proved edge instruction lists realize every
edge of the physical code, for streams of arbitrary size. -/
theorem raw_complete (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p)
    (s : Machine q) (input : Inputs f P G S)
    (hinput : InputView q f P G S p.workspace p.stride s.disk input) :
    let result := executeRaw q (code q reader f P G S p ep) s
    InputView q f P G S p.workspace p.stride result.1.disk input ∧
    (∀ e a,CommonPermutationPairs.readBit q result.1.disk (edgeBase p.workspace p.stride e)
      (commonLayout f P G S a).val=executePhysical f input e a) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<p.workspace ∨ p.childLimit≤a.val →
      result.1.disk a=s.disk a) := by
  obtain ⟨hi,he,ho⟩ := prefix_raw q reader f P G S p ep edgeCount le_rfl s input hinput
  dsimp only [code]
  refine ⟨hi,?_,ho⟩
  intro e a
  rw [executePhysical_correct]
  exact he e (edgeEnumeration e).isLt a

theorem raw_sink (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p)
    (s : Machine q) (input : Inputs f P G S)
    (hinput : InputView q f P G S p.workspace p.stride s.disk input)
    (r : Reg) (a : EdgeAddress f P G S) :
    CommonPermutationPairs.readBit q (executeRaw q (code q reader f P G S p ep) s).1.disk
      (edgeBase p.workspace p.stride (sinkWire (globalProgram Parameters.d) (globalSwap r)))
      (commonLayout f P G S a).val=
      transport (matrixLocation (1 : Matrix Index Index (Scalar f))) (input r) a := by
  obtain ⟨_,he,_⟩ := raw_complete q reader f P G S p ep s input hinput
  exact (he _ a).trans (congrFun (physicalOutput_correct f input r) a)

end
end CodedSorting.CommonRecursiveNetwork
end NetworkRun

section NetworkFrame
/-! Data-independent disk frame for the concrete recursive network. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonRecursiveNetwork
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open CommonResidentNetwork
noncomputable section
attribute [local irreducible] CommonStaticSchedule.executeRaw
attribute [local irreducible] CommonResidentNetwork.edgeCount CircuitProgram.globalProgram Parameters.W

theorem raw_outside (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p)
    (s : Machine q) (a : Fin (q.N^q.exponent))
    (ha : a.val<p.workspace ∨ p.childLimit≤a.val) :
    (executeRaw q (code q reader f P G S p ep) s).1.disk a=s.disk a := by
  let input : Inputs f P G S := fun r x =>
    readBit q s.disk (inputBase p.workspace p.stride r) (commonLayout f P G S x).val
  exact (raw_complete q reader f P G S p ep s input (by intro r x; rfl)).2.2 a ha

end
end CodedSorting.CommonRecursiveNetwork
end NetworkFrame
