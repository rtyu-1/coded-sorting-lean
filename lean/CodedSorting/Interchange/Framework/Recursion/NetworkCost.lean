import CodedSorting.Interchange.Framework.Recursion.Network

/-! The recursive network has one actual edge-program charge per edge,
plus the same concrete XOR scans as the resident construction. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace CodedSorting.CommonRecursiveNetwork
open CommonSortingNormalization CommonStaticSchedule
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open CommonNetworkInputs (ports)
open CommonResidentNetwork
noncomputable section
attribute [local irreducible] CommonResidentNetwork.edgeCount CircuitProgram.globalProgram Parameters.W

def prefixSum (value : Edge → ℕ) : (n : ℕ) → n≤edgeCount → ℕ
  | 0,_ => 0
  | n+1,hn => prefixSum value n (by omega)+value (edgeEnumeration.symm ⟨n,by omega⟩)

def edgeSum (value : Edge → ℕ) := prefixSum value edgeCount le_rfl

theorem edgeCode_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p) (e : Edge) :
    (edgeCode q reader f P G S p ep e).length=
      3*((ports e).length+1)*CommonPermutationPairs.count q (longVolume f P G S)+
      (ep.instructions e).length := by
  simp only [edgeCode,List.length_append,CommonXorAccumulator.code_length,portBases,List.length_map]

theorem edgeCode_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p) (e : Edge) :
    cost q (edgeCode q reader f P G S p ep e)=
      3*((ports e).length+1)*CommonPermutationPairs.count q (longVolume f P G S)+
      cost q (ep.instructions e) := by
  simp only [edgeCode,CommonPermutationPairs.cost_append,CommonXorAccumulator.code_cost,portBases,List.length_map]

theorem prefixCode_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p)
    (n : ℕ) (hn : n≤edgeCount) :
    (prefixCode q reader f P G S p ep n hn).length=
      3*prefixWeight n hn*CommonPermutationPairs.count q (longVolume f P G S)+
      prefixSum (fun e => (ep.instructions e).length) n hn := by
  induction n with
  | zero => change 0=3*0*_+0; omega
  | succ n ih =>
    have hi := ih (Nat.le_of_succ_le hn)
    have he := edgeCode_length q reader f P G S p ep (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩)
    change (prefixCode q reader f P G S p ep n (Nat.le_of_succ_le hn) ++
      edgeCode q reader f P G S p ep (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩)).length=_
    rw [List.length_append,hi,he]
    change _=3*(prefixWeight n (Nat.le_of_succ_le hn)+
      (ports (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩)).length+1)*CommonPermutationPairs.count q (longVolume f P G S)+
      (prefixSum (fun e => (ep.instructions e).length) n (Nat.le_of_succ_le hn)+
        (ep.instructions (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩)).length)
    ring

theorem prefixCode_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p)
    (n : ℕ) (hn : n≤edgeCount) :
    cost q (prefixCode q reader f P G S p ep n hn)=
      3*prefixWeight n hn*CommonPermutationPairs.count q (longVolume f P G S)+
      prefixSum (fun e => cost q (ep.instructions e)) n hn := by
  induction n with
  | zero => change 0=3*0*_+0; omega
  | succ n ih =>
    have hi := ih (Nat.le_of_succ_le hn)
    have he := edgeCode_cost q reader f P G S p ep (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩)
    change cost q (prefixCode q reader f P G S p ep n (Nat.le_of_succ_le hn) ++
      edgeCode q reader f P G S p ep (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩))=_
    rw [CommonPermutationPairs.cost_append,hi,he]
    change _=3*(prefixWeight n (Nat.le_of_succ_le hn)+
      (ports (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩)).length+1)*CommonPermutationPairs.count q (longVolume f P G S)+
      (prefixSum (fun e => cost q (ep.instructions e)) n (Nat.le_of_succ_le hn)+
        cost q (ep.instructions (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩)))
    ring

theorem prefixCode_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p)
    (n : ℕ) (hn : n≤edgeCount) :
    ∀ i∈prefixCode q reader f P G S p ep n hn,RespectsPC q i := by
  induction n with
  | zero => intro i hi; exact (List.not_mem_nil hi).elim
  | succ n ih =>
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact ih (Nat.le_of_succ_le hn) i hi
    · exact edgeCode_safe q reader f P G S p ep _ i hi

theorem code_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p) :
    (code q reader f P G S p ep).length=
      3*prefixWeight edgeCount le_rfl*CommonPermutationPairs.count q (longVolume f P G S)+
      prefixSum (fun e => (ep.instructions e).length) edgeCount le_rfl := by
  dsimp only [code]
  exact prefixCode_length q reader f P G S p ep edgeCount le_rfl

theorem code_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p) :
    cost q (code q reader f P G S p ep)=
      3*prefixWeight edgeCount le_rfl*CommonPermutationPairs.count q (longVolume f P G S)+
      prefixSum (fun e => cost q (ep.instructions e)) edgeCount le_rfl := by
  dsimp only [code]
  exact prefixCode_cost q reader f P G S p ep edgeCount le_rfl

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p) :
    ∀ i∈code q reader f P G S p ep,RespectsPC q i :=
  prefixCode_safe q reader f P G S p ep edgeCount le_rfl

theorem prefixSum_mono (value bound : Edge → ℕ) (h : ∀ e,value e≤bound e)
    (n : ℕ) (hn : n≤edgeCount) : prefixSum value n hn≤prefixSum bound n hn := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact Nat.add_le_add (ih (by omega)) (h _)

theorem edgeSum_mono (value bound : Edge → ℕ) (h : ∀ e,value e≤bound e) :
    edgeSum value≤edgeSum bound := prefixSum_mono value bound h edgeCount le_rfl

/-- The chronological sum contains every physical edge exactly once. -/
theorem prefixSum_eq_finSum (value : Edge → ℕ) (n : ℕ) (hn : n≤edgeCount) :
    prefixSum value n hn=
      ∑ i : Fin n,value (edgeEnumeration.symm ⟨i.val,Nat.lt_of_lt_of_le i.isLt hn⟩) := by
  induction n with
  | zero => simp only [prefixSum,Finset.univ_eq_empty,Finset.sum_empty]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    change prefixSum value n (Nat.le_of_succ_le hn)+
      value (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩)=_
    rw [ih (Nat.le_of_succ_le hn)]
    rfl

theorem edgeSum_eq_sum (value : Edge → ℕ) : edgeSum value=∑ e : Edge,value e := by
  unfold edgeSum
  rw [prefixSum_eq_finSum]
  exact edgeEnumeration.symm.sum_comp value

/-- Exact same-program I/O, expressed in the finite edge sum used by the
rank-weighted recurrence. -/
theorem code_cost_sum (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p) :
    cost q (code q reader f P G S p ep)=
      3*prefixWeight edgeCount le_rfl*CommonPermutationPairs.count q (longVolume f P G S)+
      ∑ e : Edge,cost q (ep.instructions e) := by
  rw [code_cost]
  exact congrArg (fun v => 3*prefixWeight edgeCount le_rfl*
    CommonPermutationPairs.count q (longVolume f P G S)+v)
    (edgeSum_eq_sum (fun e => cost q (ep.instructions e)))

end
end CodedSorting.CommonRecursiveNetwork
