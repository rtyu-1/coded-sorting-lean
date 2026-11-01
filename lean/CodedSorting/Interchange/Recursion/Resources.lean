import CodedSorting.Interchange.Recursion.Workspace

section Cost
/-! Total fees for the actual recursively generated Construction program.
The induction follows the builder's real stop branches and canonical rank
children. It supplies the missing bridge to Construction's pruned scalar recurrence,
without an assumed implementation kit, tree budget or execution theorem.
The same bound controls I/O fees and instruction length. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.RecursiveCost

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open ExchangeInterface ExchangeSpecialization
open RecursiveBuildConditions RecursiveCallBridge
open scoped BigOperators

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  MachineNetworkAdapter.physicalInputs OneLevelChildren.enumeration

local notation "coefficient" =>
  (24*streamCount+36+MachineNetworkActualEdges.localCoefficient)

theorem leaf_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : LeafReady q cutoff k c) :
    (RecursiveBuild.leaf q reader cutoff k c h).charge ≤
      20 * (volume radix c / width q + 1) :=
  RecursiveLeafProgram.program_charge_le q reader cutoff k c
    h.fits h.allocation h.workspace

/-- Every actual recursive child is charged once, with the exact Construction rank
budget and its actual parent-volume/streamCount size. -/
theorem build_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff k c) :
    (RecursiveBuild.build q reader cutoff k c h).charge ≤
      costBound coefficient (width q) cutoff k (volume radix c) := by
  induction k generalizing c with
  | zero =>
      exact leaf_charge_le q reader cutoff 0 c (zero_leaf h)
  | succ k ih =>
      by_cases hs : volume radix c ≤ cutoff
      · rw [RecursiveBuild.build_small q reader cutoff (k+1) c h hs,
          costBound_stop coefficient (width q) cutoff (k+1) (volume radix c) hs]
        exact leaf_charge_le q reader cutoff (k+1) c (small_leaf h hs)
      · let hn := large_node h hs
        have hsum :
            (∑ child : OneLevelChildren.Child,
              (RecursiveBuild.children q reader cutoff k c hn child).charge) ≤
            rankBudget * costBound coefficient (width q) cutoff k
              (volume radix c / streamCount) := by
          apply RecursiveCostNode.child_sum_le
          intro child
          have hi := ih
            (OneLevelExchange.childCall (nextSetup hn.shape hn.allocation hn.reserve) child)
            (hn.children child)
          exact hi.trans (le_of_eq (congrArg
            (costBound coefficient (width q) cutoff k)
            (RecursiveDescent.next_child_volume_div hn.shape hn.allocation hn.reserve child)))
        have hc := Nat.mul_le_mul_left coefficient
          (CommonResidentBase.count_le_floor q (volume radix c))
        have hncharge := RecursiveCostNode.build_node_charge_le q reader cutoff k c h hs
        rw [costBound, if_neg hs]
        exact hncharge.trans (Nat.add_le_add hc hsum)

/-- Static I/O fees of the same actual instruction sequence. -/
theorem build_cost_le (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff k c) :
    cost q (RecursiveBuild.build q reader cutoff k c h).instructions ≤
      costBound coefficient (width q) cutoff k (volume radix c) :=
  (RecursiveBuild.build q reader cutoff k c h).cost_le.trans
    (build_charge_le q reader cutoff k c h)

/-- A numerical program-counter bound, for the same generated code. -/
theorem build_length_le (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff k c) :
    (RecursiveBuild.build q reader cutoff k c h).instructions.length ≤
      costBound coefficient (width q) cutoff k (volume radix c) :=
  (RecursiveBuild.build q reader cutoff k c h).length_le.trans
    (build_charge_le q reader cutoff k c h)

/-- The previous execution theorem with actual-charge capacity replaced
by the public scalar recurrence. All conclusions concern this same run. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff k c) (s : Machine q)
    (hsize : costBound coefficient (width q) cutoff k (volume radix c) ≤ q.N^q.exponent)
    (hpc : pc q s.ram = 0) :
    let p := RecursiveBuild.build q reader cutoff k c h
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length s
    (∀ y : Fin (volume radix c), readBit q result.1.disk c.source y.val =
      readBit q s.disk c.source (permutation radix c y).val) ∧
    (∀ z : Fin (q.N^q.exponent),
      (z.val < c.source ∨ c.source + count q (volume radix c) ≤ z.val) →
      (z.val < c.buffer ∨ c.limit ≤ z.val) → result.1.disk z = s.disk z) ∧
    policy q p.instructions result.1.ram = none ∧
    result.2 ≤ costBound coefficient (width q) cutoff k (volume radix c) ∧
    Fintype.card (ResidentIndex q) ≤ q.M := by
  have hb := build_charge_le q reader cutoff k c h
  obtain ⟨hc, hf, hh, hcost, hram⟩ := RecursiveBuild.complete q reader cutoff k c h s
    (hb.trans hsize) hpc
  exact ⟨hc, hf, hh, hcost.trans hb, hram⟩

end
end CodedSorting.Construction.RecursiveCost
end Cost

section CostRate
/-! Scalar rate bounds for the concrete Construction one-level coefficient.
The existing pruned recurrence retains exactly `rankBudget` children of
volume `V / streamCount`. Its improved rate requires a cutoff of at least
`streamCount` physical blocks, so startup does not enlarge the rank/stream
multiplier. The constant chosen below depends only on the fixed network,
not on a machine, input volume, cutoff or recursion depth. Connecting this
scalar bound to the actual recursive instructions is a separate bridge. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.RecursiveCostRate

open ExchangeInterface

noncomputable section

local notation "coefficient" =>
  (24*streamCount+36+MachineNetworkActualEdges.localCoefficient)

attribute [local irreducible] TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs MachineNetworkActualEdges.localCoefficient

/-- The actual fixed network coefficient has a uniform improved rate.
The exponent is Construction.epsilon = 3/200000, not the old construction's epsilon. -/
theorem exists_rate :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b cutoff k V : Nat,
      0 < b → streamCount * b ≤ cutoff →
      (costBound coefficient b cutoff k V : ℝ) ≤
        K * (1 + (V : ℝ) / b *
          (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) :=
  exists_costBound_rate coefficient

/-- A single fixed constant chosen from the scalar theorem; it is shared
by all machines and all admissible depths, volumes and resident cutoffs. -/
def rateConstant : ℝ := Classical.choose exists_rate

theorem rateConstant_nonneg : 0 ≤ rateConstant :=
  (Classical.choose_spec exists_rate).1

theorem costBound_le_rate (b cutoff k V : Nat)
    (hb : 0 < b) (hcutoff : streamCount * b ≤ cutoff) :
    (costBound coefficient b cutoff k V : ℝ) ≤
      rateConstant * (1 + (V : ℝ) / b *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) :=
  (Classical.choose_spec exists_rate).2 b cutoff k V hb hcutoff

/-- Before solving the affine recurrence, its multiplier is precisely
rankBudget/streamCount. Both block rounding and resident stops are included. -/
theorem costBound_scaled (b cutoff k V : Nat)
    (hcutoff : streamCount * b ≤ cutoff) (hV : b ≤ V) :
    (costBound coefficient b cutoff k V : ℝ) * b ≤
      envelope coefficient k * V :=
  costBound_large_scaled coefficient b cutoff k V hcutoff hV

/-- The stronger cutoff needed by the improved I/O rate also supplies the
one-block cutoff condition used in the shared-workspace theorem. -/
theorem block_le_cutoff (b cutoff : Nat)
    (hcutoff : streamCount * b ≤ cutoff) : b ≤ cutoff := by
  have hW : 1 ≤ streamCount := by rw [streamCount_eq]; omega
  have hb : b ≤ streamCount * b := by
    simpa only [one_mul] using Nat.mul_le_mul_right b hW
  exact hb.trans hcutoff

#print axioms exists_rate
#print axioms rateConstant_nonneg
#print axioms costBound_le_rate
#print axioms costBound_scaled
#print axioms block_le_cutoff

end
end CodedSorting.Construction.RecursiveCostRate
end CostRate

section WorkspaceBounds
/-! Depth-independent bounds for the actual shared recursive scratch tail.
Block rounding is retained at every level. When the resident cutoff covers
one physical block, each non-leaf step contracts the rounded scan envelope
by at least two. The resulting reserve does not multiply by the recursion
depth or by the number of rank children. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.RecursiveWorkspaceBounds

open CommonSortingNormalization CommonPermutationPairs
open RecursiveWorkspaceBudget

noncomputable section

local notation "files" => (MachineNetworkAdapter.physicalInputs +
  MachineNetworkAdapter.nodes TensorFrameNetwork.program
    (inputs := MachineNetworkAdapter.physicalInputs))

attribute [local irreducible] TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs buckets

theorem count_le_scan (q : Configuration) (V : Nat) :
    count q V ≤ V / width q + 1 :=
  CommonResidentBase.count_le_floor q V

/-- Above a block-sized cutoff the child scan envelope contracts, including
its additive block-rounding term. The actual stream count is at least 3. -/
theorem child_scan_half (q : Configuration) (cutoff V : Nat)
    (hcutoff : width q ≤ cutoff) (hlarge : ¬ V ≤ cutoff) :
    2 * ((V / streamCount) / width q + 1) ≤ V / width q + 1 := by
  have hcomm : (V / streamCount) / width q = (V / width q) / streamCount := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
      Nat.mul_comm streamCount (width q)]
  rw [hcomm]
  have hv : 1 ≤ V / width q := by
    apply (Nat.le_div_iff_mul_le (width_pos q)).2
    omega
  have hW : 3 ≤ streamCount := by rw [streamCount_eq]; omega
  have hthree : 3 * ((V / width q) / streamCount) ≤ V / width q := by
    calc
      3 * ((V / width q) / streamCount) ≤
          streamCount * ((V / width q) / streamCount) :=
        Nat.mul_le_mul_right _ hW
      _ ≤ V / width q := Nat.mul_div_le _ _
  by_cases hu : (V / width q) / streamCount = 0
  · omega
  · omega

theorem padding_le (cutoff base V : Nat) :
    padding cutoff base V ≤ max 3 (buckets base) := by
  unfold padding
  split
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_right _ _

/-- Linear space for the same scalar reserve used by the allocator. The
explicit final padding covers either three resident blocks or all buckets. -/
theorem space_le_scan_padding (q : Configuration) (cutoff base k V : Nat)
    (hcutoff : width q ≤ cutoff) :
    space q cutoff base k V ≤
      (files + 2) * (V / width q + 1) + max 3 (buckets base) := by
  induction k generalizing V with
  | zero =>
      rw [space_zero]
      have hc := count_le_scan q V
      have hp := padding_le cutoff base V
      have hm := Nat.mul_le_mul_right (V / width q + 1)
        (show 1 ≤ files + 2 by omega)
      simp only [one_mul] at hm
      omega
  | succ k ih =>
      by_cases hs : V ≤ cutoff
      · rw [space_small q cutoff base (k+1) V hs]
        have hc := count_le_scan q V
        have hp := Nat.le_max_left 3 (buckets base)
        have hm := Nat.mul_le_mul_right (V / width q + 1)
          (show 1 ≤ files + 2 by omega)
        simp only [one_mul] at hm
        omega
      · rw [space_node q cutoff base k V hs]
        have hc := count_le_scan q V
        have hl := count_le_scan q (V / streamCount)
        have hi := ih (V / streamCount)
        have hh := child_scan_half q cutoff V hcutoff hs
        have hm := Nat.mul_le_mul_left (files + 1) hh
        have hf := Nat.mul_le_mul_left files hl
        nlinarith only [hc, hi, hm, hf]

/-- The buffered startup premise turns bucket padding into at most one
root scan whenever the root lies above the resident cutoff. -/
theorem buckets_le_scan (q : Configuration) (cutoff base V : Nat)
    (hstartup : buckets base * width q ≤ cutoff + width q)
    (hlarge : ¬ V ≤ cutoff) :
    buckets base ≤ V / width q + 1 := by
  have h : buckets base * width q ≤ V + width q := by omega
  have hdiv := (Nat.le_div_iff_mul_le (width_pos q)).2 h
  simpa only [Nat.add_div_right _ (width_pos q)] using hdiv

/-- A root-only linear disk reserve. Resident roots use their exact +3
padding; large roots absorb bucket startup into the displayed coefficient. -/
theorem space_le_scan (q : Configuration) (cutoff base k V : Nat)
    (hcutoff : width q ≤ cutoff)
    (hstartup : buckets base * width q ≤ cutoff + width q) :
    space q cutoff base k V ≤ (files + 3) * (V / width q + 1) + 3 := by
  by_cases hs : V ≤ cutoff
  · rw [space_small q cutoff base k V hs]
    have hc := count_le_scan q V
    have hm := Nat.mul_le_mul_right (V / width q + 1)
      (show 1 ≤ files + 3 by omega)
    simp only [one_mul] at hm
    omega
  · have hh := space_le_scan_padding q cutoff base k V hcutoff
    have hb := buckets_le_scan q cutoff base V hstartup hs
    have hp : max 3 (buckets base) ≤ V / width q + 1 + 3 := by
      exact max_le (by omega) (by omega)
    nlinarith only [hh, hp]

#print axioms child_scan_half
#print axioms space_le_scan_padding
#print axioms buckets_le_scan
#print axioms space_le_scan

end
end CodedSorting.Construction.RecursiveWorkspaceBounds
end WorkspaceBounds

section Capacity
/-! Fixed polynomial address capacity for the actual Construction recurrence.
This deliberately coarse integer bound is used only to fit the program
counter. The sharper Construction I/O exponent remains in RecursiveCostBounds. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace CodedSorting.Construction.RecursiveCapacity

open CommonSortingNormalization
open ExchangeInterface ExchangeSpecialization

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs MachineNetworkActualEdges.localCoefficient

local notation "coefficient" =>
  (24*streamCount+36+MachineNetworkActualEdges.localCoefficient)
local notation "files" => (MachineNetworkAdapter.physicalInputs +
  MachineNetworkAdapter.nodes TensorFrameNetwork.program
    (inputs := MachineNetworkAdapter.physicalInputs))

/-- A depth bound sufficient for finite addressability; it makes no claim
about the sharp I/O exponent. -/
theorem costBound_le_coarse (a b cutoff k V : Nat) :
    costBound a b cutoff k V ≤
      max 20 a * (rankBudget+1)^k * (V/b+1) := by
  induction k generalizing V with
  | zero =>
      simpa only [costBound, pow_zero, mul_one] using
        (Nat.mul_le_mul_right (V/b+1) (Nat.le_max_left 20 a))
  | succ k ih =>
      have hp : 1 ≤ (rankBudget+1)^k := Nat.one_le_pow _ _ (by omega)
      have ha : a ≤ max 20 a * (rankBudget+1)^k :=
        (Nat.le_max_right 20 a).trans (by
          simpa only [mul_one] using Nat.mul_le_mul_left (max 20 a) hp)
      have h20 : 20 ≤ max 20 a * (rankBudget+1)^(k+1) := by
        have hp' : 1 ≤ (rankBudget+1)^(k+1) := Nat.one_le_pow _ _ (by omega)
        have := Nat.le_max_left 20 a
        nlinarith
      by_cases hs : V ≤ cutoff
      · rw [costBound, if_pos hs]
        exact Nat.mul_le_mul_right _ h20
      · rw [costBound, if_neg hs]
        have hc : (V/streamCount)/b+1 ≤ V/b+1 :=
          Nat.add_le_add_right (Nat.div_le_div_right (Nat.div_le_self V streamCount)) 1
        calc
          _ ≤ a*(V/b+1) + rankBudget *
              (max 20 a * (rankBudget+1)^k * ((V/streamCount)/b+1)) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ (ih (V/streamCount))) _
          _ ≤ (max 20 a * (rankBudget+1)^k)*(V/b+1) + rankBudget *
              (max 20 a * (rankBudget+1)^k * (V/b+1)) :=
            Nat.add_le_add (Nat.mul_le_mul_right _ ha)
              (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc))
          _ = _ := by rw [pow_succ]; ring

/-- Finite Construction rank growth fits below the square of stream growth. -/
theorem rankBudget_add_one_le_square : rankBudget+1 ≤ streamCount^2 := by
  rw [rankBudget_eq, streamCount_eq]
  norm_num

/-- A nonempty admissible shape supplies streamCount^k ≤ N. -/
theorem costBound_le_polynomial (a b cutoff k V N : Nat)
    (hscan : V/b ≤ N) (hdepth : streamCount^k ≤ N) :
    costBound a b cutoff k V ≤ max 20 a * (N+1)^3 := by
  have hp : (rankBudget+1)^k ≤ N^2 := by
    calc
      _ ≤ (streamCount^2)^k := Nat.pow_le_pow_left rankBudget_add_one_le_square k
      _ = (streamCount^k)^2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]
      _ ≤ N^2 := Nat.pow_le_pow_left hdepth 2
  calc
    _ ≤ max 20 a * (rankBudget+1)^k * (V/b+1) := costBound_le_coarse a b cutoff k V
    _ ≤ max 20 a * (N+1)^2 * (N+1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _
        (hp.trans (Nat.pow_le_pow_left (Nat.le_succ N) 2)))
        (Nat.add_le_add_right hscan 1)
    _ = _ := by ring

/-- Empty calls stop immediately, independently of their depth. -/
theorem costBound_empty (a b cutoff k : Nat) : costBound a b cutoff k 0 = 20 := by
  rw [costBound_stop a b cutoff k 0 (Nat.zero_le cutoff)]
  simp

/-- The polynomial also covers empty inputs without a depth restriction. -/
theorem costBound_le_polynomial_or_empty (a b cutoff k V N : Nat)
    (hscan : V/b ≤ N) (hdepth : V = 0 ∨ streamCount^k ≤ N) :
    costBound a b cutoff k V ≤ max 20 a * (N+1)^3 := by
  rcases hdepth with hz | hd
  · subst V
    rw [costBound_empty]
    have hp : 1 ≤ (N+1)^3 := Nat.one_le_pow _ _ (by omega)
    have := Nat.le_max_left 20 a
    nlinarith
  · exact costBound_le_polynomial a b cutoff k V N hscan hd

/-- Absorb any fixed polynomial coefficient into one fixed extra exponent. -/
theorem absorb (N A d E : Nat) (hN : 2 ≤ N)
    (hE : d + Nat.clog 2 (A*2^d) ≤ E) : A*(N+1)^d ≤ N^E := by
  have hc : A*2^d ≤ N^(Nat.clog 2 (A*2^d)) :=
    (Nat.le_pow_clog (by omega : 1 < (2 : Nat)) _).trans (Nat.pow_le_pow_left hN _)
  have hbase : N+1 ≤ 2*N := by omega
  calc
    _ ≤ A*(2*N)^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
    _ = (A*2^d)*N^d := by rw [mul_pow]; ring
    _ ≤ N^(Nat.clog 2 (A*2^d))*N^d := Nat.mul_le_mul_right _ hc
    _ = N^(Nat.clog 2 (A*2^d)+d) := (pow_add _ _ _).symm
    _ ≤ N^E := Nat.pow_le_pow_right (by omega) (by omega)

/-- One fixed coefficient covers both the actual PC bound and root disk
layout. It depends only on the new Construction construction. -/
def capacityCoefficient : Nat := max (max 20 coefficient) (files+8)

def addressExponent : Nat := 3 + Nat.clog 2 (capacityCoefficient * 2^3)

theorem capacityCoefficient_pc : max 20 coefficient ≤ capacityCoefficient :=
  Nat.le_max_left _ _

theorem capacityCoefficient_disk : files+8 ≤ capacityCoefficient :=
  Nat.le_max_right _ _

theorem addressExponent_ge_three : 3 ≤ addressExponent := by
  unfold addressExponent
  omega

/-- A single exponent condition discharges every cubic capacity demand. -/
theorem capacity_fits (N E B : Nat) (hN : 2 ≤ N)
    (hB : B ≤ capacityCoefficient*(N+1)^3)
    (hE : addressExponent ≤ E) : B ≤ N^E :=
  hB.trans (absorb N capacityCoefficient 3 E hN hE)

/-- Explicit scalar PC capacity, including the empty-input branch. -/
theorem costBound_fits (b cutoff k V N E : Nat)
    (hN : 2 ≤ N) (hscan : V/b ≤ N)
    (hdepth : V = 0 ∨ streamCount^k ≤ N)
    (hE : addressExponent ≤ E) : costBound coefficient b cutoff k V ≤ N^E := by
  apply capacity_fits N E _ hN ?_ hE
  exact (costBound_le_polynomial_or_empty coefficient b cutoff k V N hscan hdepth).trans
    (Nat.mul_le_mul_right _ capacityCoefficient_pc)

end
end CodedSorting.Construction.RecursiveCapacity
end Capacity

section WorkspaceProgram
/-! The recursive program uses a linear bound on the initial temporary space. The base-case parameters and array shape determine allocations for all child calls. The wrapper preserves the builder's program and cost; its execution theorem takes the required instruction-count capacity as a hypothesis. 




-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.RecursiveWorkspaceProgram

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open ExchangeInterface ExchangeSpecialization
open RecursiveCallShape RecursiveBuildConditions RecursiveWorkspaceBudget

noncomputable section

local notation "files" => (MachineNetworkAdapter.physicalInputs +
  MachineNetworkAdapter.nodes TensorFrameNetwork.program
    (inputs := MachineNetworkAdapter.physicalInputs))

attribute [local irreducible] TensorFrameNetwork.program MachineNetworkAdapter.physicalInputs

/-- Physical scratch blocks, independent of the recursion depth. -/
def linearReserve (q : Configuration) (V : Nat) : Nat :=
  (files + 3) * (V / width q + 1) + 3

/-- The linear root inequality covers the exact recursive scratch reserve. -/
theorem room_of_linear (q : Configuration) (cutoff base k V buffer limit : Nat)
    (hcutoff : width q ≤ cutoff)
    (hstartup : buckets base * width q ≤ cutoff + width q)
    (hspace : buffer + linearReserve q V ≤ limit) :
    buffer + space q cutoff base k V ≤ limit :=
  (Nat.add_le_add_left
    (RecursiveWorkspaceBounds.space_le_scan q cutoff base k V hcutoff hstartup)
    buffer).trans hspace

/-- All descendant Ready obligations follow from public root data and one
linear disk-space inequality, without per-child resource certificates. -/
theorem ready_of_linear (q : Configuration) (cutoff base k : Nat) (c : Call)
    (hp : LeafParameters q cutoff base) (hcutoff : width q ≤ cutoff)
    (hshape : ShapeDepth q k c) (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + linearReserve q (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) : Ready q cutoff k c :=
  RecursiveWorkspace.ready_of_space q cutoff base k c hp hshape hwidth hsource
    (room_of_linear q cutoff base k (volume radix c) c.buffer c.limit
      hcutoff hp.startup hspace) hdisk

/-- The same concrete recursive builder, with root-only resource inputs. -/
def program (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hcutoff : width q ≤ cutoff) (hshape : ShapeDepth q k c)
    (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + linearReserve q (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) : Program q radix c :=
  RecursiveBuild.build q reader cutoff k c
    (ready_of_linear q cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk)

/-- No instruction or data-conversion pass is introduced by the space bound. -/
theorem program_instructions (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hcutoff : width q ≤ cutoff) (hshape : ShapeDepth q k c)
    (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + linearReserve q (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) :
    (program q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk).instructions =
      (RecursiveBuild.build q reader cutoff k c
        (ready_of_linear q cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk)).instructions :=
  rfl

/-- The wrapper preserves the constructed program's exact cost. -/
theorem program_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hcutoff : width q ≤ cutoff) (hshape : ShapeDepth q k c)
    (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + linearReserve q (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) :
    (program q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk).charge =
      (RecursiveBuild.build q reader cutoff k c
        (ready_of_linear q cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk)).charge :=
  rfl

/-- Correctness, disk frame, halt, actual charge, and resident RAM for the
same constructed program. Actual program-counter capacity remains explicit. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hcutoff : width q ≤ cutoff) (hshape : ShapeDepth q k c)
    (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + linearReserve q (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) (s : Machine q)
    (hsize : (program q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk).charge ≤
      q.N^q.exponent) (hpc : pc q s.ram = 0) :
    let p := program q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length s
    (∀ y : Fin (volume radix c), readBit q result.1.disk c.source y.val =
      readBit q s.disk c.source (permutation radix c y).val) ∧
    (∀ z : Fin (q.N^q.exponent),
      (z.val < c.source ∨ c.source + count q (volume radix c) ≤ z.val) →
      (z.val < c.buffer ∨ c.limit ≤ z.val) → result.1.disk z = s.disk z) ∧
    policy q p.instructions result.1.ram = none ∧ result.2 ≤ p.charge ∧
    Fintype.card (ResidentIndex q) ≤ q.M :=
  CommonFinitePermutation.complete q
    (program q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk) s hsize hpc

#print axioms room_of_linear
#print axioms ready_of_linear
#print axioms program
#print axioms program_instructions
#print axioms program_charge
#print axioms complete

end
end CodedSorting.Construction.RecursiveWorkspaceProgram
end WorkspaceProgram

section Machine
/-! One fixed inventory and address exponent for the Construction recursive exchange.
The inventory ratio is the Construction normalization threshold; the exponent is the
fixed capacity exponent already proved sufficient for the root disk and
program counter. Only the common machine's ordinary large-instance and
word-convention conditions remain when forming this configuration.
This is an inventory for the recursive exchange endpoint, not a claim
about the eventual full sorting implementation's inventory. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.RecursiveMachine

open CommonSortingNormalization SortingResourceBudget
open ExchangeSpecialization

noncomputable section

attribute [local irreducible] ExchangeSpecialization.uniform TensorFrameNetwork.program

/-- A fixed exchange inventory with an available stream reader and the
normalization ratio required by the actual Construction specialization. -/
def fixedInventory : Inventory where
  readers := 1
  writers := 1
  keys := 1
  pc := 1
  ratio := PhysicalLeafParameters.minimumRatio radix 1 streamCount

/-- Build the common machine with its existing standard size assumptions.
Neither the inventory nor the address exponent is chosen from input data. -/
def configuration (N M B w c : Nat)
    (hinput : 2 ≤ N) (hmem : M ≤ N) (hB : 0 < B) (hblock : 2*B ≤ M)
    (hword : WordConvention.Covers N w c)
    (hlarge : (reserve fixedInventory c (digits c RecursiveCapacity.addressExponent))^2 ≤ M) :
    Configuration where
  inventory := fixedInventory
  N := N
  M := M
  B := B
  w := w
  c := c
  exponent := RecursiveCapacity.addressExponent
  input_large := hinput
  memory_input := hmem
  block_pos := hB
  block_memory := hblock
  exponent_pos := (by decide : 1 ≤ (3 : Nat)).trans RecursiveCapacity.addressExponent_ge_three
  word_convention := hword
  memory_large := hlarge

variable (N M B w c : Nat)
  (hinput : 2 ≤ N) (hmem : M ≤ N) (hB : 0 < B) (hblock : 2*B ≤ M)
  (hword : WordConvention.Covers N w c)
  (hlarge : (reserve fixedInventory c (digits c RecursiveCapacity.addressExponent))^2 ≤ M)

/-- Reader zero in the fixed exchange inventory. -/
def reader : Fin (configuration N M B w c hinput hmem hB hblock hword hlarge).inventory.readers :=
  ⟨0, by change 0 < (1 : Nat); decide⟩

theorem reader_val : (reader N M B w c hinput hmem hB hblock hword hlarge).val = 0 := rfl

theorem inventory_threshold : PhysicalLeafParameters.minimumRatio radix 1 streamCount ≤
    (configuration N M B w c hinput hmem hB hblock hword hlarge).inventory.ratio := le_rfl

/-- The inventory choice discharges the Construction parameter-normalization premise. -/
theorem normalized : RecursiveParameters.Normalized
    (configuration N M B w c hinput hmem hB hblock hword hlarge) :=
  RecursiveParameters.normalized_of_inventory _
    (inventory_threshold N M B w c hinput hmem hB hblock hword hlarge)

/-- The address exponent condition is discharged by the fixed choice. -/
theorem exponent_sufficient : RecursiveCapacity.addressExponent ≤
    (configuration N M B w c hinput hmem hB hblock hword hlarge).exponent := le_rfl

#print axioms configuration
#print axioms reader
#print axioms inventory_threshold
#print axioms normalized
#print axioms exponent_sufficient

end
end CodedSorting.Construction.RecursiveMachine
end Machine

section RootLayout
/-! A canonical root for the actual Construction exchange recursion. Public root
dimensions determine an exact word count, the source starts at zero, and
the temporary interval begins immediately after its source blocks. A fixed
polynomial bounds the complete root allocation from its input word count.
The base width remains a parameter for the separate leaf-parameter choice. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.RecursiveRootLayout

open CommonSortingNormalization CommonPermutationPairs
open ExchangeInterface ExchangeSpecialization RecursiveCallShape

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs

local notation "files" => (MachineNetworkAdapter.physicalInputs +
  MachineNetworkAdapter.nodes TensorFrameNetwork.program
    (inputs := MachineNetworkAdapter.physicalInputs))

/-- The actual scalar root word count, including both exchanged fields. -/
def rootWords (_q : Configuration) (base k lanes G S : Nat) : Nat :=
  ((lanes*streamCount^k)*((radix^(ambientDimension^k*base))*G)) *
    ((radix^(ambientDimension^k*base))*S)

def rootVolume (q : Configuration) (base k lanes G S : Nat) : Nat :=
  rootWords q base k lanes G S * q.w

/-- The concrete root has a separated source followed by the proved
linear shared-workspace reserve. No per-child addresses are supplied. -/
def rootCall (q : Configuration) (base k lanes G S : Nat) : Call :=
  depthCall q k base lanes G S 0
    (count q (rootVolume q base k lanes G S))
    (count q (rootVolume q base k lanes G S) +
      RecursiveWorkspaceProgram.linearReserve q (rootVolume q base k lanes G S))

theorem root_volume (q : Configuration) (base k lanes G S : Nat) :
    volume radix (rootCall q base k lanes G S) = rootVolume q base k lanes G S := by
  change ((lanes*streamCount^k)*((radix^(ambientDimension^k*base))*G)) *
      ((radix^(ambientDimension^k*base))*(S*q.w)) =
    (((lanes*streamCount^k)*((radix^(ambientDimension^k*base))*G)) *
      ((radix^(ambientDimension^k*base))*S))*q.w
  simp only [Nat.mul_assoc]

theorem root_width (q : Configuration) (base k lanes G S : Nat) :
    (rootCall q base k lanes G S).fieldWidth = ambientDimension^k*base := rfl

theorem root_shape (q : Configuration) (base k lanes G S : Nat)
    (hbase : 0 < base) (hG : 0 < G) (hS : 0 < S) :
    ShapeDepth q k (rootCall q base k lanes G S) :=
  depthCall_shape q k base lanes G S 0 _ _ hbase hG hS

theorem root_source_separate (q : Configuration) (base k lanes G S : Nat) :
    (rootCall q base k lanes G S).source +
      count q (volume radix (rootCall q base k lanes G S)) ≤
      (rootCall q base k lanes G S).buffer := by
  rw [root_volume]
  exact (Nat.zero_add _).le

theorem root_space (q : Configuration) (base k lanes G S : Nat) :
    (rootCall q base k lanes G S).buffer +
      RecursiveWorkspaceProgram.linearReserve q
        (volume radix (rootCall q base k lanes G S)) ≤
      (rootCall q base k lanes G S).limit := by
  rw [root_volume]
  exact le_rfl

private theorem word_le_block_bits (q : Configuration) : q.w ≤ width q := by
  have hb : 1 ≤ q.block := by have := CommonLeafProgram.block_positive q; omega
  exact (Nat.one_mul q.w).symm.trans_le (Nat.mul_le_mul_right q.w hb)

theorem root_volume_le_blocks (q : Configuration) (base k lanes G S : Nat) :
    rootVolume q base k lanes G S ≤ rootWords q base k lanes G S * width q :=
  Nat.mul_le_mul_left _ (word_le_block_bits q)

/-- Complete scan blocks never exceed the root's public input word budget. -/
theorem root_scan_le (q : Configuration) (base k lanes G S : Nat)
    (hwords : rootWords q base k lanes G S ≤ q.N) :
    rootVolume q base k lanes G S / width q ≤ q.N := by
  apply Nat.div_le_of_le_mul
  simpa only [Nat.mul_comm q.N (width q)] using
    (root_volume_le_blocks q base k lanes G S).trans
      (Nat.mul_le_mul_right (width q) hwords)

/-- Rounding the final partial block still fits within one block per word. -/
theorem root_count_le (q : Configuration) (base k lanes G S : Nat)
    (hwords : rootWords q base k lanes G S ≤ q.N) :
    count q (rootVolume q base k lanes G S) ≤ q.N :=
  LayoutConversion.blockCount_minimal _ _ _ (width_pos q)
    ((root_volume_le_blocks q base k lanes G S).trans
      (Nat.mul_le_mul_right (width q) hwords))

/-- A nonempty root retains the full stream-count factor at its entrance.
The zero-lane root is handled independently by the resident stop branch. -/
theorem stream_power_le_words (q : Configuration) (base k lanes G S : Nat)
    (hlanes : 0 < lanes) (hG : 0 < G) (hS : 0 < S) :
    streamCount^k ≤ rootWords q base k lanes G S := by
  have hQ : 0 < radix^(ambientDimension^k*base) := pow_pos radix_prime.pos _
  calc
    streamCount^k ≤ lanes*streamCount^k := by
      simpa only [one_mul] using Nat.mul_le_mul_right (streamCount^k)
        (show 1 ≤ lanes by omega)
    _ ≤ (lanes*streamCount^k)*((radix^(ambientDimension^k*base))*G) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos hQ hG)
    _ ≤ rootWords q base k lanes G S :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos hQ hS)

private theorem allocation_polynomial (F N C scan : Nat)
    (hC : C ≤ N) (hscan : scan ≤ N) :
    C + ((F+3)*(scan+1)+3) ≤ (F+8)*(N+1)^3 := by
  have hm := Nat.mul_le_mul_left (F+3) (Nat.add_le_add_right hscan 1)
  have hp : N+1 ≤ (N+1)^3 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (show 1 ≤ N+1 by omega) (show 1 ≤ 3 by omega)
  calc
    C + ((F+3)*(scan+1)+3) ≤ N + ((F+3)*(N+1)+3) :=
      Nat.add_le_add hC (Nat.add_le_add_right hm 3)
    _ ≤ (F+8)*(N+1) := by nlinarith
    _ ≤ (F+8)*(N+1)^3 := Nat.mul_le_mul_left _ hp

/-- One fixed polynomial covers the canonical root's entire disk interval.
Its coefficient is the same raw network-file count used by the allocator. -/
theorem root_limit_bound (q : Configuration) (base k lanes G S : Nat)
    (hwords : rootWords q base k lanes G S ≤ q.N) :
    (rootCall q base k lanes G S).limit ≤ (files+8)*(q.N+1)^3 :=
  allocation_polynomial files q.N (count q (rootVolume q base k lanes G S))
    (rootVolume q base k lanes G S / width q)
    (root_count_le q base k lanes G S hwords) (root_scan_le q base k lanes G S hwords)

end
end CodedSorting.Construction.RecursiveRootLayout
end RootLayout

section Resources
/-! All numerical resources for the canonical Construction root.
The chosen memory parameters, counted input words and one fixed machine
address exponent supply the entire recursive allocation and code capacity.
No caller-supplied leaf, child, disk-reserve or actual-charge certificate
remains. Empty roots use the resident stop without a false depth bound. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.RecursiveResources

open CommonSortingNormalization CommonPermutationPairs
open ExchangeInterface ExchangeSpecialization RecursiveCallShape
open RecursiveParameters RecursiveRootLayout

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  MachineNetworkAdapter.physicalInputs MachineNetworkActualEdges.localCoefficient

local notation "coefficient" =>
  (24*streamCount+36+MachineNetworkActualEdges.localCoefficient)

/-- The actual root call with its base width selected from machine memory. -/
def root (q : Configuration) (k lanes G S : Nat) : Call :=
  rootCall q (chosenBase q) k lanes G S

theorem root_shape (q : Configuration) (k lanes G S : Nat)
    (hnormal : Normalized q) (hG : 0 < G) (hS : 0 < S) :
    ShapeDepth q k (root q k lanes G S) :=
  RecursiveRootLayout.root_shape q (chosenBase q) k lanes G S
    (chosenBase_pos q hnormal) hG hS

theorem root_width (q : Configuration) (k lanes G S : Nat) :
    (root q k lanes G S).fieldWidth = ambientDimension^k * chosenBase q := rfl

/-- The canonical complete disk interval fits the configured address space. -/
theorem root_disk_fits (q : Configuration) (k lanes G S : Nat)
    (hwords : rootWords q (chosenBase q) k lanes G S ≤ q.N)
    (hexponent : RecursiveCapacity.addressExponent ≤ q.exponent) :
    (root q k lanes G S).limit ≤ q.N^q.exponent :=
  RecursiveCapacity.capacity_fits q.N q.exponent _ q.input_large
    ((root_limit_bound q (chosenBase q) k lanes G S hwords).trans
      (Nat.mul_le_mul_right _ RecursiveCapacity.capacityCoefficient_disk)) hexponent

/-- The fixed exponent also covers the real program's numerical charge
recurrence. The empty root is handled without any restriction on depth. -/
theorem root_code_fits (q : Configuration) (k lanes G S : Nat)
    (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords q (chosenBase q) k lanes G S ≤ q.N)
    (hexponent : RecursiveCapacity.addressExponent ≤ q.exponent) :
    costBound coefficient (width q) (cutoff q) k (volume radix (root q k lanes G S)) ≤
      q.N^q.exponent := by
  have hv := root_volume q (chosenBase q) k lanes G S
  have hscan : volume radix (root q k lanes G S) / width q ≤ q.N :=
    (congrArg (fun V => V / width q) hv).trans_le
      (root_scan_le q (chosenBase q) k lanes G S hwords)
  have hdepth : volume radix (root q k lanes G S) = 0 ∨ streamCount^k ≤ q.N := by
    by_cases hz : lanes = 0
    · left
      exact hv.trans (by simp only [rootVolume, rootWords, hz, Nat.zero_mul])
    · right
      exact (stream_power_le_words q (chosenBase q) k lanes G S
        (Nat.pos_of_ne_zero hz) hG hS).trans hwords
  exact RecursiveCapacity.costBound_fits (width q) (cutoff q) k
    (volume radix (root q k lanes G S)) q.N q.exponent q.input_large hscan hdepth hexponent

/-- All descendants are numerically admissible, from the selected global
parameters and a counted root input, not from per-descendant assumptions. -/
theorem ready (q : Configuration) (k lanes G S : Nat)
    (hnormal : Normalized q) (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords q (chosenBase q) k lanes G S ≤ q.N)
    (hexponent : RecursiveCapacity.addressExponent ≤ q.exponent) :
    RecursiveBuildConditions.Ready q (cutoff q) k (root q k lanes G S) :=
  RecursiveWorkspaceProgram.ready_of_linear q (cutoff q) (chosenBase q) k
    (root q k lanes G S) (leafParameters q hnormal)
    (RecursiveCostRate.block_le_cutoff (width q) (cutoff q) (cutoff_child q hnormal))
    (root_shape q k lanes G S hnormal hG hS) (root_width q k lanes G S)
    (root_source_separate q (chosenBase q) k lanes G S)
    (root_space q (chosenBase q) k lanes G S)
    (root_disk_fits q k lanes G S hwords hexponent)

end
end CodedSorting.Construction.RecursiveResources
end Resources
