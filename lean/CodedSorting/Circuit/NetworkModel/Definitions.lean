import CodedSorting.Interchange.Framework.Memory.ExchangeShapeProgram
import CodedSorting.Shared.Memory.XorAccumulator

/-! Actual finite-machine execution of a topologically ordered XOR network.
Each edge owns a fresh disk slab. Its ports are added by real scans and its
address map is the supplied, already proved, instruction program. The graph
may contain arbitrary storage registers; only the explicitly provided input
files enter the input view. No successful network run is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace CodedSorting.Construction.MachineNetwork
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Disk Machine)
open scoped BigOperators
noncomputable section

structure Circuit (inputs nodes V : Nat) where
  ports : Fin nodes → List (Fin (inputs+nodes))
  prior : ∀ e p, p ∈ ports e → p.val < inputs+e.val
  permutation : Fin nodes → Equiv.Perm (Fin V)

def nodeFile {inputs nodes : Nat} (e : Fin nodes) : Fin (inputs+nodes) :=
  ⟨inputs+e.val, by omega⟩

structure Layout (q : Configuration) (inputs nodes V : Nat) where
  workspace : Nat
  stride : Nat
  buffer : Nat
  limit : Nat
  count_le_stride : count q V ≤ stride
  files_le_buffer : workspace+(inputs+nodes)*stride ≤ buffer
  buffer_le_limit : buffer ≤ limit
  fit : limit ≤ q.N^q.exponent

namespace Layout
variable {q : Configuration} {inputs nodes V : Nat}
def base (p : Layout q inputs nodes V) (file : Fin (inputs+nodes)) : Nat :=
  p.workspace+file.val*p.stride

theorem base_end_le (p : Layout q inputs nodes V) (file : Fin (inputs+nodes)) :
    p.base file+p.stride ≤ p.buffer := by
  have h := Nat.mul_le_mul_right p.stride (Nat.succ_le_of_lt file.isLt)
  dsimp [base]
  nlinarith [p.files_le_buffer]

theorem base_fits (p : Layout q inputs nodes V) (file : Fin (inputs+nodes)) :
    p.base file+count q V ≤ q.N^q.exponent := by
  have := p.base_end_le file
  have := p.count_le_stride
  have := p.buffer_le_limit
  have := p.fit
  omega

theorem base_separate (p : Layout q inputs nodes V) (a b : Fin (inputs+nodes))
    (hne : a ≠ b) : p.base a+count q V ≤ p.base b ∨
      p.base b+count q V ≤ p.base a := by
  have hs : a.val ≠ b.val := fun h => hne (Fin.ext h)
  have hc := p.count_le_stride
  rcases lt_or_gt_of_ne hs with h | h
  · left
    have := Nat.mul_le_mul_right p.stride (Nat.succ_le_of_lt h)
    dsimp [base]; nlinarith
  · right
    have := Nat.mul_le_mul_right p.stride (Nat.succ_le_of_lt h)
    dsimp [base]; nlinarith

theorem bit_before_buffer (p : Layout q inputs nodes V) (file : Fin (inputs+nodes))
    (i : Fin V) :
    (CommonColumnSplit.address q (p.base file) (i.val/width q)).val < p.buffer := by
  have hi := bit_block_lt q i
  have hf := p.base_fits file
  have hb := p.base_end_le file
  have hc := p.count_le_stride
  rw [CommonColumnSplit.address_val q _ _ (by omega)]
  omega

theorem bit_outside_file (p : Layout q inputs nodes V)
    (written other : Fin (inputs+nodes)) (hne : other ≠ written) (i : Fin V) :
    (CommonColumnSplit.address q (p.base other) (i.val/width q)).val < p.base written ∨
    p.base written+count q V ≤
      (CommonColumnSplit.address q (p.base other) (i.val/width q)).val := by
  have hi := bit_block_lt q i
  have hf := p.base_fits other
  have ha : p.base other+i.val/width q < q.N^q.exponent := by omega
  simp only [CommonColumnSplit.address_val q (p.base other) (i.val/width q) ha]
  rcases p.base_separate other written hne with h | h
  · left; omega
  · right; exact h.trans (Nat.le_add_right _ _)

end Layout

variable {q : Configuration} {inputs nodes V : Nat}

abbrev Programs (C : Circuit inputs nodes V) (p : Layout q inputs nodes V) :=
  (e : Fin nodes) → CommonFinitePermutation.Program q V (p.base (nodeFile e))
    p.buffer p.limit (C.permutation e)

abbrev Values (inputs nodes V : Nat) := Fin (inputs+nodes) → Fin V → CodedSorting.Circuit.Bit

/-- A symbolic, local algebraic identity of the given network. It contains
no disk state or machine execution premise. -/
def LocalEq (C : Circuit inputs nodes V) (value : Values inputs nodes V) : Prop :=
  ∀ e y, value (nodeFile e) y =
    ((C.ports e).map (fun port => value port (C.permutation e y))).sum

def View (p : Layout q inputs nodes V) (n : Nat) (disk : Disk q)
    (value : Values inputs nodes V) : Prop :=
  ∀ file, file.val < inputs+n → ∀ y : Fin V,
    readBit q disk (p.base file) y.val = value file y

def portBases (C : Circuit inputs nodes V) (p : Layout q inputs nodes V)
    (e : Fin nodes) : List Nat := (C.ports e).map p.base

def edgeCode (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p) (e : Fin nodes) :=
  CommonXorAccumulator.code q reader V (p.base (nodeFile e)) (portBases C p e) ++
    (ep e).instructions

/-- Every XOR port predates its fresh output slab. -/
theorem port_ne_target (C : Circuit inputs nodes V) (e : Fin nodes)
    (port : Fin (inputs+nodes)) (hp : port ∈ C.ports e) : port ≠ nodeFile e := by
  have h := C.prior e port hp
  intro he
  rw [he] at h
  exact (Nat.lt_irrefl _ h)

theorem edge_raw (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p) (e : Fin nodes)
    (s : Machine q) (value : Values inputs nodes V)
    (hloc : LocalEq C value) (hview : View p e.val s.disk value) :
    let result := executeRaw q (edgeCode reader C p ep e) s
    (∀ y : Fin V, readBit q result.1.disk (p.base (nodeFile e)) y.val =
      value (nodeFile e) y) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val < p.base (nodeFile e) ∨ p.base (nodeFile e)+count q V ≤ a.val) →
      (a.val < p.buffer ∨ p.limit ≤ a.val) → result.1.disk a=s.disk a) := by
  have hs : ∀ x ∈ portBases C p e, x+count q V ≤ q.N^q.exponent := by
    intro x hx
    obtain ⟨port, _, rfl⟩ := List.mem_map.mp hx
    exact p.base_fits port
  have hsep : ∀ x ∈ portBases C p e,
      CommonXorAccumulator.Separate q V (p.base (nodeFile e)) x := by
    intro x hx
    obtain ⟨port, hp, rfl⟩ := List.mem_map.mp hx
    exact p.base_separate port (nodeFile e) (port_ne_target C e port hp)
  let mid := (executeRaw q (CommonXorAccumulator.code q reader V
    (p.base (nodeFile e)) (portBases C p e)) s).1
  obtain ⟨hm, hf, _⟩ := CommonXorAccumulator.raw_complete q reader V
    (p.base (nodeFile e)) (portBases C p e) s (p.base_fits _) hs hsep
  dsimp only
  rw [edgeCode, raw_append]
  refine ⟨?_, ?_⟩
  · intro y
    rw [(ep e).correct, hm, hloc e y]
    simp only [portBases, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro port hp
    exact hview port (C.prior e port hp) (C.permutation e y)
  · intro a ha hb
    exact ((ep e).frame mid a ha hb).trans (hf a ha)

def prefixCode (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p) :
    (n : Nat) → n ≤ nodes → List (Instruction q)
  | 0, _ => []
  | n+1, hn => prefixCode reader C p ep n (by omega) ++
      edgeCode reader C p ep ⟨n, by omega⟩

def code (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p) :=
  prefixCode reader C p ep nodes le_rfl

theorem prefix_raw (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p)
    (n : Nat) (hn : n ≤ nodes) (s : Machine q) (value : Values inputs nodes V)
    (hloc : LocalEq C value) (hinput : View p 0 s.disk value) :
    let result := executeRaw q (prefixCode reader C p ep n hn) s
    View p n result.1.disk value ∧
    (∀ a : Fin (q.N^q.exponent), a.val < p.workspace ∨ p.limit ≤ a.val →
      result.1.disk a=s.disk a) := by
  induction n with
  | zero => exact ⟨hinput, fun _ _ => rfl⟩
  | succ n ih =>
    let e : Fin nodes := ⟨n, by omega⟩
    let mid := (executeRaw q (prefixCode reader C p ep n (by omega)) s).1
    obtain ⟨hm, ho⟩ := ih (by omega)
    obtain ⟨he, hf⟩ := edge_raw reader C p ep e mid value hloc hm
    change View p (n+1)
      (executeRaw q (prefixCode reader C p ep n (by omega) ++ edgeCode reader C p ep e) s).1.disk value ∧ _
    rw [raw_append]
    refine ⟨?_, ?_⟩
    · intro file hfile y
      by_cases hnew : file = nodeFile e
      · subst file
        exact he y
      · have hold : file.val < inputs+n := by
          have hne : file.val ≠ inputs+n := fun h => hnew (Fin.ext h)
          omega
        have hkeep : readBit q (executeRaw q (edgeCode reader C p ep e) mid).1.disk
            (p.base file) y.val = readBit q mid.disk (p.base file) y.val := by
          unfold readBit
          rw [hf]
          · exact p.bit_outside_file (nodeFile e) file hnew y
          · exact Or.inl (p.bit_before_buffer file y)
        exact hkeep.trans (hm file hold y)
    · intro a ha
      have htarget : a.val < p.base (nodeFile e) ∨
          p.base (nodeFile e)+count q V ≤ a.val := by
        have hb := p.base_end_le (nodeFile e)
        have hc := p.count_le_stride
        have hl := p.buffer_le_limit
        rcases ha with ha | ha
        · left; exact ha.trans_le (Nat.le_add_right _ _)
        · right; omega
      have hbuffer : a.val < p.buffer ∨ p.limit ≤ a.val := by
        rcases ha with ha | ha
        · left
          exact ha.trans_le ((Nat.le_add_right _ _).trans p.files_le_buffer)
        · exact Or.inr ha
      rw [prefixCode, raw_append]
      exact (hf a htarget hbuffer).trans (ho a ha)

/-- All allocated output slabs contain the specified physical network
values after this actual instruction sequence. -/
theorem raw_correct (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p)
    (s : Machine q) (value : Values inputs nodes V)
    (hloc : LocalEq C value) (hinput : View p 0 s.disk value) :
    let result := executeRaw q (code reader C p ep) s
    (∀ file y, readBit q result.1.disk (p.base file) y.val=value file y) ∧
    (∀ a : Fin (q.N^q.exponent), a.val < p.workspace ∨ p.limit ≤ a.val →
      result.1.disk a=s.disk a) := by
  obtain ⟨hv, hf⟩ := prefix_raw reader C p ep nodes le_rfl s value hloc hinput
  exact ⟨fun file => hv file file.isLt, hf⟩


/-- Frame safety is independent of the symbolic values used in correctness. -/
theorem edge_frame (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p) (e : Fin nodes)
    (s : Machine q) (a : Fin (q.N^q.exponent))
    (ht : a.val < p.base (nodeFile e) ∨ p.base (nodeFile e)+count q V ≤ a.val)
    (hb : a.val < p.buffer ∨ p.limit ≤ a.val) :
    (executeRaw q (edgeCode reader C p ep e) s).1.disk a=s.disk a := by
  have hs : ∀ x ∈ portBases C p e, x+count q V ≤ q.N^q.exponent := by
    intro x hx
    obtain ⟨port, _, rfl⟩ := List.mem_map.mp hx
    exact p.base_fits port
  have hsep : ∀ x ∈ portBases C p e,
      CommonXorAccumulator.Separate q V (p.base (nodeFile e)) x := by
    intro x hx
    obtain ⟨port, hp, rfl⟩ := List.mem_map.mp hx
    exact p.base_separate port (nodeFile e) (port_ne_target C e port hp)
  obtain ⟨_, hf, _⟩ := CommonXorAccumulator.raw_complete q reader V
    (p.base (nodeFile e)) (portBases C p e) s (p.base_fits _) hs hsep
  rw [edgeCode, raw_append, (ep e).frame _ a ht hb]
  exact hf a ht

theorem prefix_frame (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p)
    (n : Nat) (hn : n ≤ nodes) (s : Machine q)
    (a : Fin (q.N^q.exponent)) (ha : a.val < p.workspace ∨ p.limit ≤ a.val) :
    (executeRaw q (prefixCode reader C p ep n hn) s).1.disk a=s.disk a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht : a.val < p.base (nodeFile (inputs := inputs) ⟨n, Nat.lt_of_succ_le hn⟩) ∨
        p.base (nodeFile (inputs := inputs) ⟨n, Nat.lt_of_succ_le hn⟩)+count q V ≤ a.val := by
      have hb := p.base_end_le (nodeFile ⟨n, Nat.lt_of_succ_le hn⟩)
      have hc := p.count_le_stride
      have hl := p.buffer_le_limit
      rcases ha with ha | ha
      · left; exact ha.trans_le (Nat.le_add_right _ _)
      · right; omega
    have hb : a.val < p.buffer ∨ p.limit ≤ a.val := by
      rcases ha with ha | ha
      · left; exact ha.trans_le ((Nat.le_add_right _ _).trans p.files_le_buffer)
      · exact Or.inr ha
    rw [prefixCode, raw_append, edge_frame reader C p ep _ _ a ht hb]
    exact ih (Nat.le_of_succ_le hn)

theorem code_frame (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p)
    (s : Machine q) (a : Fin (q.N^q.exponent))
    (ha : a.val < p.workspace ∨ p.limit ≤ a.val) :
    (executeRaw q (code reader C p ep) s).1.disk a=s.disk a :=
  prefix_frame reader C p ep nodes le_rfl s a ha

def prefixSum (value : Fin nodes → Nat) : (n : Nat) → n ≤ nodes → Nat
  | 0, _ => 0
  | n+1, hn => prefixSum value n (by omega)+value ⟨n, by omega⟩

theorem prefixSum_eq_finSum (value : Fin nodes → Nat) (n : Nat) (hn : n ≤ nodes) :
    prefixSum value n hn = ∑ i : Fin n, value ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ := by
  induction n with
  | zero => simp only [prefixSum, Finset.univ_eq_empty, Finset.sum_empty]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    change prefixSum value n (by omega)+value ⟨n, by omega⟩ = _
    rw [ih (by omega)]
    rfl

def edgeCharge (C : Circuit inputs nodes V) (p : Layout q inputs nodes V)
    (ep : Programs C p) (e : Fin nodes) : Nat :=
  3*((C.ports e).length+1)*count q V+(ep e).charge

def charge (C : Circuit inputs nodes V) (p : Layout q inputs nodes V)
    (ep : Programs C p) : Nat := ∑ e, edgeCharge C p ep e

theorem edge_resources (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p) (e : Fin nodes) :
    cost q (edgeCode reader C p ep e) ≤ edgeCharge C p ep e ∧
    (edgeCode reader C p ep e).length ≤ edgeCharge C p ep e := by
  constructor
  · rw [edgeCode, cost_append, CommonXorAccumulator.code_cost]
    simpa only [edgeCharge, portBases, List.length_map] using
      Nat.add_le_add_left (ep e).cost_le (3*((C.ports e).length+1)*count q V)
  · rw [edgeCode, List.length_append, CommonXorAccumulator.code_length]
    simpa only [edgeCharge, portBases, List.length_map] using
      Nat.add_le_add_left (ep e).length_le (3*((C.ports e).length+1)*count q V)

theorem edge_safe (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p) (e : Fin nodes) :
    ∀ i ∈ edgeCode reader C p ep e, RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact CommonXorAccumulator.code_safe q reader _ _ _ i hi
  · exact (ep e).safe i hi

theorem prefix_resources (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p) (n : Nat) (hn : n ≤ nodes) :
    cost q (prefixCode reader C p ep n hn) ≤ prefixSum (edgeCharge C p ep) n hn ∧
    (prefixCode reader C p ep n hn).length ≤ prefixSum (edgeCharge C p ep) n hn ∧
    (∀ i ∈ prefixCode reader C p ep n hn, RespectsPC q i) := by
  induction n with
  | zero => exact ⟨le_rfl, le_rfl, by simp [prefixCode]⟩
  | succ n ih =>
    obtain ⟨hc, hl, hs⟩ := ih (Nat.le_of_succ_le hn)
    obtain ⟨hec, hel⟩ := edge_resources reader C p ep ⟨n, by omega⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [prefixCode, cost_append]
      exact Nat.add_le_add hc hec
    · rw [prefixCode, List.length_append]
      exact Nat.add_le_add hl hel
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hs i hi
      · exact edge_safe reader C p ep _ i hi

theorem code_resources (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p) :
    cost q (code reader C p ep) ≤ charge C p ep ∧
    (code reader C p ep).length ≤ charge C p ep ∧
    (∀ i ∈ code reader C p ep, RespectsPC q i) := by
  have h := prefix_resources reader C p ep nodes le_rfl
  rw [prefixSum_eq_finSum] at h
  exact h

/-- Explicit local scan overhead plus precisely one charge for each actual
edge program. This is the quantity passed into the sorting recurrence. -/
theorem charge_eq (C : Circuit inputs nodes V) (p : Layout q inputs nodes V)
    (ep : Programs C p) :
    charge C p ep =
      3*(∑ e, ((C.ports e).length+1))*count q V + ∑ e, (ep e).charge := by
  simp only [charge, edgeCharge]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]

/-- Substituting the proved edge bounds produces one fixed local scan
coefficient plus the charges of the genuinely invoked child programs. -/
theorem charge_le (C : Circuit inputs nodes V) (p : Layout q inputs nodes V)
    (ep : Programs C p) (edgeLocal childCharge : Fin nodes → Nat)
    (h : ∀ e, (ep e).charge ≤ edgeLocal e*count q V+childCharge e) :
    charge C p ep ≤
      (3*(∑ e, ((C.ports e).length+1))+∑ e, edgeLocal e)*count q V +
        ∑ e, childCharge e := by
  rw [charge_eq]
  calc
    _ ≤ 3*(∑ e, ((C.ports e).length+1))*count q V +
        ∑ e, (edgeLocal e*count q V+childCharge e) :=
      Nat.add_le_add_left (Finset.sum_le_sum (fun e _ => h e)) _
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
      ring

/-- The logical controller executes the same concrete instruction sequence,
halts, obeys the physical RAM bound, and pays the proved total I/O charge. -/
theorem complete (reader : Fin q.inventory.readers) (C : Circuit inputs nodes V)
    (p : Layout q inputs nodes V) (ep : Programs C p)
    (s : Machine q) (value : Values inputs nodes V)
    (hloc : LocalEq C value) (hinput : View p 0 s.disk value)
    (hsize : charge C p ep ≤ q.N^q.exponent) (hpc : pc q s.ram=0) :
    let instructions := code reader C p ep
    let result := ControlledNormalization.runLogical (policy q instructions)
      instructions.length s
    (∀ file y, readBit q result.1.disk (p.base file) y.val=value file y) ∧
    (∀ a : Fin (q.N^q.exponent), a.val < p.workspace ∨ p.limit ≤ a.val →
      result.1.disk a=s.disk a) ∧
    policy q instructions result.1.ram=none ∧ result.2 ≤ charge C p ep ∧
    Fintype.card (ResidentIndex q) ≤ q.M := by
  obtain ⟨hc, hl, hs⟩ := code_resources reader C p ep
  obtain ⟨hv, hf⟩ := raw_correct reader C p ep s value hloc hinput
  obtain ⟨hd, hh, hcost, hm⟩ := run_code_disk q (code reader C p ep)
    (hl.trans hsize) hs s hpc
  exact ⟨by rw [hd]; exact hv, by rw [hd]; exact hf,
    hh, hcost.trans_le hc, hm⟩

#print axioms raw_correct
#print axioms code_resources
#print axioms charge_eq
#print axioms complete

end
end CodedSorting.Construction.MachineNetwork
