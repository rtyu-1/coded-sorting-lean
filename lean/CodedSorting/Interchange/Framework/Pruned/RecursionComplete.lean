import CodedSorting.Interchange.Framework.Resident.Base
import CodedSorting.Shared.Memory.Buffered.Permutation

section CostBound
/-! Numerical cost bound for the common-machine recursion with resident
cutoff. The buffered base retains its additive bucket charge until the
nonresident condition absorbs it. This module supplies an arithmetic
majorant; the generated-program certificate must connect its actual budget
to this same recurrence before the final execution theorem uses the bound.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace CodedSorting.CommonRecursiveExchange.Pruned
open CommonSortingNormalization CommonPermutationPairs
open RecursiveExchange PhysicalFieldPacking Circuit Address
noncomputable section
attribute [local irreducible] CommonResidentNetwork.edgeCount CircuitProgram.globalProgram Parameters.W

def parentCoefficient : ℕ := 72*Parameters.m+12*Parameters.W+6

def childCoefficient : ℕ :=
  12*Parameters.W+3*CommonResidentNetwork.prefixWeight CommonResidentNetwork.edgeCount le_rfl+
    CommonRankEdge.constructionConstant

-- Keep this closed coefficient syntactically expanded in exported bounds:
-- implicit conversion of its alias can force kernel evaluation of the
-- enormous, fixed network edge sum.
local notation "childCoefficientValue" =>
  (12*Parameters.W+3*CommonResidentNetwork.prefixWeight CommonResidentNetwork.edgeCount le_rfl+
    CommonRankEdge.constructionConstant)

def localCoefficient : ℕ := max 20 (parentCoefficient+childCoefficientValue)

/-- The base and resident-stop envelopes coincide. An expanded node pays
for its scans and exactly S recursive child invocations of volume V/W. -/
def costBound (b cutoff : ℕ) : ℕ → ℕ → ℕ
  | 0,V => 20*(V/b+1)
  | k+1,V => if V≤cutoff then 20*(V/b+1)
      else localCoefficient*(V/b+1)+Parameters.S*costBound b cutoff k (V/Parameters.W)

@[simp] theorem costBound_zero (b cutoff V : ℕ) :
    costBound b cutoff 0 V=20*(V/b+1) := rfl

theorem costBound_stop (b cutoff k V : ℕ) (hV : V≤cutoff) :
    costBound b cutoff k V=20*(V/b+1) := by
  cases k <;> simp only [costBound,if_pos hV]

theorem costBound_step (b cutoff k V : ℕ) (hV : cutoff<V) :
    costBound b cutoff (k+1) V=localCoefficient*(V/b+1)+
      Parameters.S*costBound b cutoff k (V/Parameters.W) := by
  rw [costBound,if_neg (Nat.not_le.mpr hV)]

theorem count_le_scan (q : Configuration) (V : ℕ) :
    count q V≤V/width q+1 :=
  ScanProgram.ceil_le_floor_add_one V (width q) (width_pos q)

theorem resident_leaf_le (q : Configuration) (V : ℕ) :
    2*count q V+3≤20*(V/width q+1) := by
  have hc:=count_le_scan q V
  have h : ∀ n c : ℕ,c≤n+1 → 2*c+3≤20*(n+1) := by
    intro n c hh
    omega
  exact h _ _ hc

/-- Outside the cutoff, the K bucket-boundary startups are bounded by one
scan envelope. K is a public bucket count, never a payload-dependent value. -/
theorem buckets_le_scan (b K cutoff V : ℕ) (hb : 0<b)
    (hstartup : K*b≤cutoff+b) (hV : cutoff<V) :
    K≤V/b+1 := by
  have hk : K*b≤V+b := hstartup.trans (Nat.add_le_add_right hV.le b)
  have hd := (Nat.le_div_iff_mul_le hb).mpr hk
  simpa only [Nat.add_div_right V hb] using hd

theorem buffered_leaf_le (q : Configuration) (K cutoff V : ℕ)
    (hstartup : K*width q≤cutoff+width q) (hV : cutoff<V) :
    4*count q V+2*K+1≤20*(V/width q+1) := by
  have hc:=count_le_scan q V
  have hk:=buckets_le_scan (width q) K cutoff V (width_pos q) hstartup hV
  have h : ∀ n c k : ℕ,c≤n+1 → k≤n+1 → 4*c+2*k+1≤20*(n+1) := by
    intro n c k hcn hkn
    omega
  exact h _ _ _ hc hk

/-- The child scan is no larger than the parent scan. The fixed coefficient
includes all local network work, leaving recursive child budgets separate. -/
theorem node_local_le (q : Configuration) (V : ℕ) :
    parentCoefficient*count q V+childCoefficientValue*count q (V/Parameters.W)≤
      localCoefficient*(V/width q+1) := by
  have hp:=count_le_scan q V
  have hc:=count_le_scan q (V/Parameters.W)
  have hd : (V/Parameters.W)/width q≤V/width q :=
    Nat.div_le_div_right (Nat.div_le_self V Parameters.W)
  have hc' : count q (V/Parameters.W)≤V/width q+1 := by omega
  calc
    _ ≤ parentCoefficient*(V/width q+1)+childCoefficientValue*(V/width q+1) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hp) (Nat.mul_le_mul_left _ hc')
    _ = (parentCoefficient+childCoefficientValue)*(V/width q+1) :=
      (Nat.add_mul parentCoefficient childCoefficientValue (V/width q+1)).symm
    _ ≤ localCoefficient*(V/width q+1) :=
      Nat.mul_le_mul_right _ (Nat.le_max_right _ _)

def boundConstant : ℝ :=
  CallTree.uniformConstant (2*(localCoefficient : ℝ)) (2*20)

theorem boundConstant_nonneg : 0≤boundConstant :=
  CallTree.uniformConstant_nonneg _ _ (by positivity) (by norm_num)

/-- Exact arithmetic representation of costBound by the existing pruned
call tree. The generated program is connected to costBound separately. -/
theorem costBound_eq_tree (b cutoff k V : ℕ) :
    costBound b cutoff k V=CallTree.cost (CallTree.prunedBuild 1 cutoff
      (fun V=>20*(V/b+1)) (fun _ V=>localCoefficient*(V/b+1)) k V) := by
  induction k generalizing V with
  | zero => rfl
  | succ k ih =>
    rw [costBound,CallTree.prunedBuild]
    split_ifs with hfit
    · rfl
    · simp only [CallTree.cost,Finset.sum_const,Finset.card_univ,child_count,smul_eq_mul]
      rw [←ih]

/-- All startup terms remain charged. The cutoff prevents recursively
creating sub-block descendants, yielding the rank-weighted S/W growth. -/
theorem costBound_scaled (b cutoff k V : ℕ) (hcut : Parameters.W*b≤cutoff) :
    (costBound b cutoff k V : ℝ)*b≤boundConstant*
      (b+(V : ℝ)*(Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) := by
  rw [costBound_eq_tree]
  apply CallTree.pruned_cost_with_startup 1 cutoff b
    (fun V=>20*(V/b+1)) (fun _ V=>localCoefficient*(V/b+1))
    (2*(localCoefficient : ℝ)) 20 hcut (by positivity) (by norm_num)
  · intro v
    have hd:=Nat.div_mul_le_self v b
    have hb : (20*(v/b+1))*b≤20*(b+v) := by nlinarith
    exact_mod_cast hb
  · intro j v hlarge
    have hW : 1≤Parameters.W := by rw [Parameters.W_value]; omega
    have hwb : b≤Parameters.W*b := by
      simpa only [one_mul] using Nat.mul_le_mul_right b hW
    have hv : b≤v := hwb.trans (hcut.trans hlarge.le)
    have hd:=Nat.div_mul_le_self v b
    have hs : (v/b+1)*b≤2*v := by nlinarith
    have hb:=Nat.mul_le_mul_left localCoefficient hs
    have hb' : (localCoefficient*(v/b+1))*b≤(2*localCoefficient)*v := by nlinarith
    exact_mod_cast hb'

theorem costBound_transfers (b cutoff k V : ℕ) (hb : 0<b)
    (hcut : Parameters.W*b≤cutoff) :
    (costBound b cutoff k V : ℝ)≤boundConstant*
      (1+(V : ℝ)/b*(Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) := by
  have hbr : (0 : ℝ)<b := by exact_mod_cast hb
  apply (mul_le_mul_right hbr).mp
  calc
    _ ≤ boundConstant*(b+(V : ℝ)*(Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) :=
      costBound_scaled b cutoff k V hcut
    _ = _ := by field_simp

end
end CodedSorting.CommonRecursiveExchange.Pruned
end CostBound

section Recursion
/-! Workspace, resident-buffer conditions, and public recursive budgets for
resident or buffered leaves. This does not change the existing recursion tree or
its internal network implementation. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonRecursiveExchange.Pruned
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking
open CommonRecursiveExchangeCost PhysicalStreamCursor Address Circuit
noncomputable section
attribute [local irreducible] CommonResidentNetwork.edgeCount CircuitProgram.globalProgram Parameters.W

def buckets (f : ℕ) : ℕ := (radix^f)*(radix^f)

def space (q : Configuration) : {f P G S : ℕ} → Tree q f P G S → ℕ
  | f,P,G,S,.leaf _ _ _ _ => count q (ScalarVolume f P G S)+buckets f+3
  | _,_,_,_,.node f R G S _ _ children =>
      parentCount q f R G S+CommonResidentNetwork.fileCount*childCount q f R G S+
        childCount q f R G S+∑ c : Child,space q (children c)

/-- Small leaves load the entire live file into the existing resident bank;
larger leaves need one block per bucket. This condition contains dimensions
only, with no assumed child execution or correctness predicate. -/
def Fits (q : Configuration) (cutoff : ℕ) : {f P G S : ℕ} → Tree q f P G S → Prop
  | f,P,G,S,.leaf _ _ _ _ =>
      if ScalarVolume f P G S≤cutoff then ScalarVolume f P G S≤CommonExchangeLeaf.bankBits q
      else buckets f*q.block≤CommonExchangeLeaf.bankWords q
  | _,_,_,_,.node _ _ _ _ _ _ children => ∀ c : Child,Fits q cutoff (children c)

theorem old_space_le (q : Configuration) {f P G S : ℕ} (t : Tree q f P G S) :
    CommonRecursiveExchange.space q t≤space q t := by
  induction t with
  | leaf => simp only [CommonRecursiveExchange.space,space]; omega
  | node f R G S hG hS children ih =>
    have hh := Finset.sum_le_sum (fun c (_ : c∈(Finset.univ : Finset Child)) => ih c)
    simp only [CommonRecursiveExchange.space,space,parentCount,childCount] at *
    omega

theorem volume_le_space (q : Configuration) {f P G S : ℕ} (t : Tree q f P G S) :
    count q (ScalarVolume f P G S)≤space q t :=
  (CommonRecursiveExchange.volume_le_space q t).trans (old_space_le q t)

theorem child_space_le (q : Configuration) (f R G S : ℕ)
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c)) (c : Child) :
    space q (children c)≤∑ d : Child,space q (children d) :=
  Finset.single_le_sum (f:=fun d : Child => space q (children d))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

def allocation (q : Configuration) (f R G S source buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S)
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c))
    (hs : source+count q (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w))≤buffer)
    (hw : buffer+space q (.node f R G S hG hS children)≤limit)
    (hl : limit≤q.N^q.exponent) : NodeAllocation q f R G S source buffer limit :=
  treeAllocation q f R G S source buffer limit hG hS children hs
    ((Nat.add_le_add_left (old_space_le q (.node f R G S hG hS children)) buffer).trans hw) hl

theorem child_workspace (q : Configuration) (f R G S buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S)
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c))
    (hw : buffer+space q (.node f R G S hG hS children)≤limit) (c : Child) :
    childBase q f R G S buffer+space q (children c)≤limit := by
  have hc := child_space_le q f R G S children c
  dsimp only [space] at hw
  dsimp only [childBase,networkBase]
  omega

def leafCharge (q : Configuration) (cutoff f P G S : ℕ) : ℕ :=
  if ScalarVolume f P G S≤cutoff then 20*(ScalarVolume f P G S/width q+1)
  else 4*count q (ScalarVolume f P G S)+2*buckets f+1

def budget (q : Configuration) (cutoff : ℕ) : {f P G S : ℕ} → Tree q f P G S → ℕ
  | f,P,G,S,.leaf _ _ _ _ => leafCharge q cutoff f P G S
  | _,_,_,_,.node f R G S hG hS children =>
      (72*Parameters.m+12*Parameters.W)*parentCount q f R G S+
      12*Parameters.W*blockCount q.block (longVolume f R G S)+
      networkCharge q f R G (S*q.w) hG
        (Nat.mul_pos hS (by have:=q.word_width; omega)) (fun c=>budget q cutoff (children c))+
      6*parentCount q f R G S

/-- The unchanged internal-node cost plus exactly the selected child
budgets. The improved leaf charge is already part of this recurrence. -/
theorem budget_node_le (q : Configuration) (cutoff f R G S : ℕ) (hG : 0<G) (hS : 0<S)
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c)) :
    budget q cutoff (.node f R G S hG hS children)≤
      (72*Parameters.m+12*Parameters.W+6)*parentCount q f R G S+
      (12*Parameters.W+3*CommonResidentNetwork.prefixWeight CommonResidentNetwork.edgeCount le_rfl+
        CommonRankEdge.constructionConstant)*childCount q f R G S+
      ∑ c : Child,budget q cutoff (children c) := by
  have hh := CommonRecursiveExchange.networkCharge_le q f R G (S*q.w) hG
    (Nat.mul_pos hS (by have:=q.word_width; omega)) (fun c=>budget q cutoff (children c))
  have hc : blockCount q.block (longVolume f R G S)=childCount q f R G S :=
    (CommonOneLevelAllocation.local_count q f R G S).symm
  dsimp only [budget]
  rw [hc]
  change _≤(72*Parameters.m+12*Parameters.W+6)*parentCount q f R G S+
    (12*Parameters.W+3*CommonResidentNetwork.prefixWeight CommonResidentNetwork.edgeCount le_rfl+
      CommonRankEdge.constructionConstant)*count q (longVolume f R G (S*q.w))+_
  dsimp only [childCount]
  nlinarith

end
end CodedSorting.CommonRecursiveExchange.Pruned
end Recursion

section Volume
/-! Exact volumes at a recursive machine call. Each selected child keeps
one complete role stream, including every spectator coordinate. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace CodedSorting.CommonPrunedVolume
open CommonSortingNormalization CommonPermutationPairs
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking
open CommonRecursiveExchange CommonRecursivePacking
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m Parameters.S

theorem width_positive : 0<Parameters.W := by
  rw [Parameters.W_value]
  omega

theorem child_scalar_volume (f R G S : ℕ) (c : Child) :
    ScalarVolume f (childP f R c) (childG f G c) (childS f S c)=
      longVolume f R G S := child_volume f R G S c

theorem parent_scalar_volume (f R G S : ℕ) :
    ScalarVolume (Parameters.m*f) (R*Parameters.W) G S=
      Parameters.W*longVolume f R G S := by
  rw [packedVolume]
  unfold longVolume
  ac_rfl

theorem child_volume_div_raw (f R G S : ℕ) (c : Child) :
    ScalarVolume f (childP f R c) (childG f G c) (childS f S c)=
      ScalarVolume (Parameters.m*f) (R*Parameters.W) G S/Parameters.W := by
  rw [child_scalar_volume,parent_scalar_volume,Nat.mul_div_cancel_left _ width_positive]

/-- Every generated child has exactly one W-th of its parent's bit volume. -/
theorem child_volume_div (q : Configuration) (f R G S : ℕ) (c : Child) :
    ScalarVolume f (childP f R c) (childG f G c) (childS f (S*q.w) c)=
      ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w)/Parameters.W :=
  child_volume_div_raw f R G (S*q.w) c

/-- The same equality after canonical prefix and word-aligned suffix casts. -/
theorem canonical_child_volume_div (q : Configuration) (base k rows G S : ℕ) (c : Child) :
    ScalarVolume (base*Parameters.m^k)
      ((rows*beforeCard (base*Parameters.m^k) (childRow c))*Parameters.W^k)
      (childG (base*Parameters.m^k) G c)
      (childS (base*Parameters.m^k) S c*q.w)=
    ScalarVolume (base*Parameters.m^(k+1)) (rows*Parameters.W^(k+1)) G (S*q.w)/Parameters.W := by
  rw [←RecursiveCallShape.selected_prefix,←child_suffix_words,next_width,next_prefix]
  exact child_volume_div q _ _ _ _ c

theorem count_mono (q : Configuration) {U V : ℕ} (h : U≤V) :
    count q U≤count q V := by
  unfold count PhysicalStreamCursor.blockCount
  exact Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h _) _)

theorem child_count_eq (q : Configuration) (f R G S : ℕ) (c : Child) :
    count q (ScalarVolume f (childP f R c) (childG f G c) (childS f (S*q.w) c))=
      childCount q f R G S := by
  rw [child_scalar_volume]
  rfl

theorem parent_count_eq (q : Configuration) (f R G S : ℕ) :
    count q (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w))=
      parentCount q f R G S := by
  rw [packedVolume]
  rfl

theorem child_count_le_parent (q : Configuration) (f R G S : ℕ) :
    childCount q f R G S≤parentCount q f R G S := by
  apply count_mono
  have hm := Nat.mul_le_mul_right (longVolume f R G (S*q.w))
    (show 1≤Parameters.W from width_positive)
  simpa only [one_mul,←parent_scalar_volume,packedVolume] using hm

theorem sum_child_constant (C : ℕ) : (∑ _c : Child,C)=Parameters.S*C := by
  simp only [Finset.sum_const,Finset.card_univ,child_count,smul_eq_mul]

theorem sum_child_le (charge : Child→ℕ) (C : ℕ) (h : ∀ c,charge c≤C) :
    (∑ c : Child,charge c)≤Parameters.S*C := by
  calc
    _≤∑ _c : Child,C := Finset.sum_le_sum (fun c _ => h c)
    _=_ := sum_child_constant C

/-- Any volume-only child bound reduces to one common argument V/W. -/
theorem sum_child_volume_bound (q : Configuration) (f R G S : ℕ)
    (bound : ℕ→ℕ) (charge : Child→ℕ)
    (h : ∀ c,charge c≤bound
      (ScalarVolume f (childP f R c) (childG f G c) (childS f (S*q.w) c))) :
    (∑ c : Child,charge c)≤Parameters.S*
      bound (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w)/Parameters.W) := by
  apply sum_child_le
  intro c
  simpa only [child_volume_div] using h c

end
end CodedSorting.CommonPrunedVolume
end Volume

section RecursionBuild
/-! The complete recursion tree uses actual resident leaves below the cutoff
and buffered leaves otherwise. Every selected child is generated recursively; no
child correctness or execution oracle is an input. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonRecursiveExchange.Pruned
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking
open CommonRecursiveExchangeCost PhysicalStreamCursor Address Circuit
noncomputable section
attribute [local irreducible] CommonResidentNetwork.edgeCount CircuitProgram.globalProgram Parameters.W

/-- Construct actual instructions from the public recursion tree and
explicit memory/disk bounds. Public volume selects each leaf implementation. -/
def build (q : Configuration) (reader : Fin q.inventory.readers) (cutoff : ℕ)
    {f P G S : ℕ} (t : Tree q f P G S) :
    Fits q cutoff t → ∀ source buffer limit : ℕ,
      source+count q (ScalarVolume f P G S)≤buffer →
      buffer+space q t≤limit → limit≤q.N^q.exponent →
      Program q f P G S source buffer limit := by
  induction t with
  | leaf f P G S =>
    intro hf source buffer limit hs hw hl
    by_cases hsmall : ScalarVolume f P G S≤cutoff
    · exact CommonResidentBase.program q reader f P G S source buffer limit
        (by simpa only [Fits,if_pos hsmall] using hf) hs
        (by dsimp only [space,buckets] at hw; omega) hl
    · exact CommonBufferedBase.program q reader f P G S source buffer limit
        (by simpa only [Fits,if_neg hsmall] using hf) hs
        (by dsimp only [space,buckets] at hw; omega) hl
  | node f R G S hG hS children ih =>
    intro hf source buffer limit hs hw hl
    let a := allocation q f R G S source buffer limit hG hS children hs hw hl
    apply nodeProgram q reader f R G S source buffer limit hG hS a
    intro c
    apply ih c (hf c)
      (CommonResidentNetwork.scratchBase (networkBase q f R G S buffer) (childCount q f R G S))
      (childBase q f R G S buffer) limit
    · rw [ScalarVolume,child_volume]
      exact scratch_separate q f R G S source buffer limit a
    · exact child_workspace q f R G S buffer limit hG hS children hw c
    · exact hl

theorem build_charge (q : Configuration) (reader : Fin q.inventory.readers) (cutoff : ℕ)
    {f P G S : ℕ} (t : Tree q f P G S) :
    ∀ (hf : Fits q cutoff t) (source buffer limit : ℕ)
      (hs : source+count q (ScalarVolume f P G S)≤buffer)
      (hw : buffer+space q t≤limit) (hl : limit≤q.N^q.exponent),
      (build q reader cutoff t hf source buffer limit hs hw hl).charge=budget q cutoff t := by
  induction t with
  | leaf f P G S =>
    intro hf source buffer limit hs hw hl
    simp only [build,budget,leafCharge]
    split_ifs <;> rfl
  | node f R G S hG hS children ih =>
    intro hf source buffer limit hs hw hl
    simp only [build,nodeProgram,nodeCharge,budget,CommonRecursiveOuterResources.outsideNetwork,
      CommonRecursiveOuter.parentBlocks,CommonRecursiveOuter.parentBits,CommonRecursiveOuter.suffix,
      CommonRecursiveOuter.liveBlocks,CommonRecursiveOuter.words,outerSetup,parentCount]
    congr 2
    apply congrArg (networkCharge q f R G (S*q.w) hG _)
    funext c
    exact ih c _ _ _ _ _ _ _

theorem build_cost_le (q : Configuration) (reader : Fin q.inventory.readers) (cutoff : ℕ)
    {f P G S : ℕ} (t : Tree q f P G S) (hf : Fits q cutoff t) (source buffer limit : ℕ)
    (hs : source+count q (ScalarVolume f P G S)≤buffer)
    (hw : buffer+space q t≤limit) (hl : limit≤q.N^q.exponent) :
    cost q (build q reader cutoff t hf source buffer limit hs hw hl).instructions≤budget q cutoff t :=
  (build q reader cutoff t hf source buffer limit hs hw hl).cost_le.trans_eq
    (build_charge q reader cutoff t hf source buffer limit hs hw hl)

theorem build_length_le (q : Configuration) (reader : Fin q.inventory.readers) (cutoff : ℕ)
    {f P G S : ℕ} (t : Tree q f P G S) (hf : Fits q cutoff t) (source buffer limit : ℕ)
    (hs : source+count q (ScalarVolume f P G S)≤buffer)
    (hw : buffer+space q t≤limit) (hl : limit≤q.N^q.exponent) :
    (build q reader cutoff t hf source buffer limit hs hw hl).instructions.length≤budget q cutoff t :=
  (build q reader cutoff t hf source buffer limit hs hw hl).length_le.trans_eq
    (build_charge q reader cutoff t hf source buffer limit hs hw hl)

end
end CodedSorting.CommonRecursiveExchange.Pruned
end RecursionBuild

section RecursionFamily
/-! A generated recursion family that stops as soon as its current file
fits in the resident bank. The tree, all leaf-memory conditions and its
uniform scalar I/O bound are constructed together, so no successful child
execution or unproved recursion certificate is supplied by the caller. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonRecursiveExchange.Pruned
open CommonSortingNormalization CommonPermutationPairs RecursiveExchange RecursiveExchangeCost
open PhysicalFieldPacking CommonRecursivePacking RecursiveCallShape
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m Parameters.S radix
attribute [local irreducible] CommonResidentNetwork.edgeCount CircuitProgram.globalProgram
local notation "childCoefficientValue" => (12*Parameters.W+
  3*CommonResidentNetwork.prefixWeight CommonResidentNetwork.edgeCount le_rfl+
  CommonRankEdge.constructionConstant)

abbrev Certified (q : Configuration) (cutoff k f P G S : ℕ) :=
  {t : Tree q f P G S // Fits q cutoff t ∧
    budget q cutoff t≤costBound (width q) cutoff k (ScalarVolume f P G S)}

private def castCertified (q : Configuration) (cutoff k : ℕ)
    {f P G S f' P' G' S' : ℕ}
    (hf : f=f') (hP : P=P') (hG : G=G') (hS : S=S')
    (t : Certified q cutoff k f P G S) : Certified q cutoff k f' P' G' S' := by
  subst f'
  subst P'
  subst G'
  subst S'
  exact t

private theorem fits_node (q : Configuration) (cutoff f R G S : ℕ)
    (hG : 0<G) (hS : 0<S)
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c))
    (hc : ∀ c,Fits q cutoff (children c)) :
    Fits q cutoff (Tree.node f R G S hG hS children) := hc

private def residentLeaf (q : Configuration) (cutoff k f P G S : ℕ)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hsmall : ScalarVolume f P G S≤cutoff) : Certified q cutoff k f P G S := by
  refine ⟨Tree.leaf f P G S,?_,?_⟩
  · change (if ScalarVolume f P G S≤cutoff then _ else _)
    rw [if_pos hsmall]
    exact hsmall.trans hresident
  · change leafCharge q cutoff f P G S≤_
    rw [leafCharge,if_pos hsmall,costBound_stop _ _ _ _ hsmall]

private def bufferedLeaf (q : Configuration) (cutoff base P G S : ℕ)
    (hlarge : cutoff<ScalarVolume base P G S)
    (hfit : buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : buckets base*width q≤cutoff+width q) : Certified q cutoff 0 base P G S := by
  refine ⟨Tree.leaf base P G S,?_,?_⟩
  · change (if ScalarVolume base P G S≤cutoff then _ else _)
    rw [if_neg (Nat.not_le_of_gt hlarge)]
    exact hfit
  · change leafCharge q cutoff base P G S≤_
    rw [leafCharge,if_neg (Nat.not_le_of_gt hlarge),costBound_zero]
    exact buffered_leaf_le q (buckets base) cutoff (ScalarVolume base P G S) hstartup hlarge

private theorem child_count_div (q : Configuration) (f R G S : ℕ) :
    childCount q f R G S=
      count q (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w)/Parameters.W) := by
  rw [CommonPrunedVolume.parent_scalar_volume,
    Nat.mul_div_cancel_left _ CommonPrunedVolume.width_positive]
  rfl

private theorem node_local (q : Configuration) (f R G S : ℕ) :
    parentCoefficient*parentCount q f R G S+childCoefficientValue*childCount q f R G S≤
      localCoefficient*(ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w)/width q+1) := by
  have hn := node_local_le q (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w))
  have hp := CommonPrunedVolume.parent_count_eq q f R G S
  rw [hp,←child_count_div q f R G S] at hn
  exact hn

private theorem parent_coefficient : parentCoefficient=72*Parameters.m+12*Parameters.W+6 := rfl

private theorem node_budget_coefficients (q : Configuration) (cutoff f R G S : ℕ)
    (hG : 0<G) (hS : 0<S)
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c)) :
    budget q cutoff (Tree.node f R G S hG hS children)≤
      parentCoefficient*parentCount q f R G S+childCoefficientValue*childCount q f R G S+
        ∑ c : Child,budget q cutoff (children c) := by
  have he := congrArg (fun a : ℕ =>
    a*parentCount q f R G S+childCoefficientValue*childCount q f R G S+
      ∑ c : Child,budget q cutoff (children c)) parent_coefficient.symm
  exact (budget_node_le q cutoff f R G S hG hS children).trans_eq he

private theorem children_budget_bound (q : Configuration) (cutoff k f R G S : ℕ)
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c))
    (hc : ∀ c,budget q cutoff (children c)≤costBound (width q) cutoff k
      (ScalarVolume f (childP f R c) (childG f G c) (childS f (S*q.w) c))) :
    (∑ c : Child,budget q cutoff (children c))≤Parameters.S*costBound (width q) cutoff k
      (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w)/Parameters.W) :=
  CommonPrunedVolume.sum_child_volume_bound q f R G S
    (costBound (width q) cutoff k) (fun c => budget q cutoff (children c)) hc

private theorem node_budget (q : Configuration) (cutoff k f R G S : ℕ)
    (hG : 0<G) (hS : 0<S)
    (hlarge : cutoff<ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w))
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c))
    (hc : ∀ c,budget q cutoff (children c)≤costBound (width q) cutoff k
      (ScalarVolume f (childP f R c) (childG f G c) (childS f (S*q.w) c))) :
    budget q cutoff (Tree.node f R G S hG hS children)≤
      costBound (width q) cutoff (k+1)
        (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w)) := by
  have hs := children_budget_bound q cutoff k f R G S children hc
  have hb := node_budget_coefficients q cutoff f R G S hG hS children
  have hn := node_local q f R G S
  exact (hb.trans (Nat.add_le_add hn hs)).trans_eq
    (costBound_step (width q) cutoff k _ hlarge).symm

/-- The only base-width conditions concern its actual bucket buffers and
their startup charge. The volume test is repeated before every descent. -/
def canonicalFitted (q : Configuration) (cutoff base : ℕ) :
    (k rows G S : ℕ) → (hG : 0<G) → (hS : 0<S) →
      (hresident : cutoff≤CommonExchangeLeaf.bankBits q) →
      (hfit : buckets base*q.block≤CommonExchangeLeaf.bankWords q) →
      (hstartup : buckets base*width q≤cutoff+width q) →
      Certified q cutoff k (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w)
  | 0,rows,G,S,_,_,hresident,hfit,hstartup => by
      let leaf : Certified q cutoff 0 base rows G (S*q.w) :=
        if hsmall : ScalarVolume base rows G (S*q.w)≤cutoff then
          residentLeaf q cutoff 0 base rows G (S*q.w) hresident hsmall
        else bufferedLeaf q cutoff base rows G (S*q.w) (Nat.lt_of_not_ge hsmall) hfit hstartup
      exact castCertified q cutoff 0 (by simp only [pow_zero,Nat.mul_one])
        (by simp only [pow_zero,Nat.mul_one]) rfl rfl leaf
  | k+1,rows,G,S,hG,hS,hresident,hfit,hstartup => by
      by_cases hsmall : ScalarVolume (base*Parameters.m^(k+1))
          (rows*Parameters.W^(k+1)) G (S*q.w)≤cutoff
      · exact residentLeaf q cutoff (k+1) _ _ G (S*q.w) hresident hsmall
      · let f := base*Parameters.m^k
        let R := rows*Parameters.W^k
        let children : (c : Child) →
            Certified q cutoff k f (childP f R c) (childG f G c) (childS f (S*q.w) c) :=
          fun c => castCertified q cutoff k rfl (selected_prefix base k rows c).symm rfl
            (child_suffix_words f S q.w c).symm
            (canonicalFitted q cutoff base k (rows*beforeCard f (childRow c))
              (childG f G c) (childS f S c)
              (child_gap_positive f G c hG) (childS_pos f S c hS) hresident hfit hstartup)
        let t := Tree.node f R G S hG hS (fun c => (children c).val)
        have ht : Fits q cutoff t := fits_node q cutoff f R G S hG hS _
          (fun c => (children c).property.1)
        have hl : cutoff<ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w) := by
          simpa only [f,R,next_width,next_prefix] using Nat.lt_of_not_ge hsmall
        have hb : budget q cutoff t≤costBound (width q) cutoff (k+1)
            (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w)) :=
          node_budget q cutoff k f R G S hG hS hl _ (fun c => (children c).property.2)
        exact castCertified q cutoff (k+1) (next_width base k).symm
          (next_prefix rows k).symm rfl rfl ⟨t,ht,hb⟩

end
end CodedSorting.CommonRecursiveExchange.Pruned
end RecursionFamily

section TreeComplete
/-! The pruned public instruction program: correctness and resource charges
refer to the same finite-RAM, finite-disk run, including both kinds of leaf. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonRecursiveExchange.Pruned
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking Address Circuit
attribute [local irreducible] build ControlledNormalization.runLogical
noncomputable section

theorem tree_complete (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) {f P G S : ℕ} (t : Tree q f P G S)
    (hf : Fits q cutoff t) (source buffer limit : ℕ)
    (hs : source+count q (ScalarVolume f P G S)≤buffer)
    (hw : buffer+space q t≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q) (hsize : budget q cutoff t≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let p := build q reader cutoff t hf source buffer limit hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    (∀ a : ScalarAddress f P G S,
      readBit q result.1.disk source (scalarLayout f P G S a).val=
      readBit q s.disk source (scalarLayout f P G S (exchange a)).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q (ScalarVolume f P G S)≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧ result.2≤budget q cutoff t ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  have hc := build_charge q reader cutoff t hf source buffer limit hs hw hl
  have h := CommonRecursiveExchange.complete q f P G S source buffer limit
    (build q reader cutoff t hf source buffer limit hs hw hl) s (hc.trans_le hsize) hpc
  simpa only [hc] using h

end
end CodedSorting.CommonRecursiveExchange.Pruned
end TreeComplete

section RecursionComplete
/-! The improved exponent bounds the same common-machine execution whose
instructions, data movement, disk frame, halt and resident RAM are proved.
The generated recursion carries its numerical budget certificate with it.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonRecursiveExchange.Pruned
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open RecursiveExchange PhysicalFieldPacking Address Circuit
attribute [local irreducible] canonicalFitted build costBound ControlledNormalization.runLogical
noncomputable section

def canonicalProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k rows G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : buckets base*width q≤cutoff+width q)
    (hs : source+count q (ScalarVolume (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w))≤buffer)
    (hw : buffer+space q (canonicalFitted q cutoff base k rows G S hG hS
      hresident hfit hstartup).val≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w) source buffer limit :=
  build q reader cutoff (canonicalFitted q cutoff base k rows G S hG hS
    hresident hfit hstartup).val
    (canonicalFitted q cutoff base k rows G S hG hS hresident hfit hstartup).property.1
    source buffer limit hs hw hl

attribute [local irreducible] canonicalProgram

theorem canonical_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k rows G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : buckets base*width q≤cutoff+width q)
    (hs : source+count q (ScalarVolume (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w))≤buffer)
    (hw : buffer+space q (canonicalFitted q cutoff base k rows G S hG hS
      hresident hfit hstartup).val≤limit)
    (hl : limit≤q.N^q.exponent) :
    (canonicalProgram q reader cutoff base k rows G S source buffer limit hG hS
      hresident hfit hstartup hs hw hl).charge≤
      costBound (width q) cutoff k
        (ScalarVolume (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w)) := by
  unfold canonicalProgram
  rw [build_charge]
  exact (canonicalFitted q cutoff base k rows G S hG hS hresident hfit hstartup).property.2

/-- All conclusions concern one run. The only capacity premises concern
its actual allocated disk and public instruction counter, not child execution. -/
theorem canonical_bound (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k rows G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : buckets base*width q≤cutoff+width q)
    (hcut : Parameters.W*width q≤cutoff)
    (hs : source+count q (ScalarVolume (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w))≤buffer)
    (hw : buffer+space q (canonicalFitted q cutoff base k rows G S hG hS
      hresident hfit hstartup).val≤limit)
    (hl : limit≤q.N^q.exponent) (s : Machine q)
    (hsize : costBound (width q) cutoff k
      (ScalarVolume (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w))≤q.N^q.exponent)
    (hpc : pc q s.ram=0) :
    let p := canonicalProgram q reader cutoff base k rows G S source buffer limit hG hS
      hresident hfit hstartup hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    (∀ a : ScalarAddress (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w),
      readBit q result.1.disk source
        (scalarLayout (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w) a).val=
      readBit q s.disk source
        (scalarLayout (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w) (exchange a)).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q
        (ScalarVolume (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w))≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧
    (result.2 : ℝ)≤boundConstant*
      (1+(ScalarVolume (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w) : ℝ)/width q*
        (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  let p := canonicalProgram q reader cutoff base k rows G S source buffer limit hG hS
    hresident hfit hstartup hs hw hl
  have hc := canonical_charge_le q reader cutoff base k rows G S source buffer limit hG hS
    hresident hfit hstartup hs hw hl
  obtain ⟨hout,hframe,hhalt,hcost,hram⟩ := CommonRecursiveExchange.complete q _ _ _ _
    source buffer limit p s (hc.trans hsize) hpc
  refine ⟨hout,hframe,hhalt,?_,hram⟩
  exact (Nat.cast_le.mpr (hcost.trans hc)).trans
    (costBound_transfers (width q) cutoff k _ (width_pos q) hcut)

end
end CodedSorting.CommonRecursiveExchange.Pruned
end RecursionComplete
