import CodedSorting.Shared.Memory.ScanProgram
import CodedSorting.Interchange.Framework.Recursion.Network

section RankEdgeScan
/-! Actual factor scans returning to their original stream allocation.
An odd number of scans receives one charged identity copy. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonRankEdgeScan
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs ScanProgram
open CommonLeafProgram (Machine)
noncomputable section

def identityPass (V : ℕ) : Pass V :=
  .streams 1 (Equiv.refl _) (fun _ => 0) (by intro x y h _; exact h)

def padded {V : ℕ} (ps : List (Pass V)) : List (Pass V) :=
  if ps.length%2=0 then ps else ps++[identityPass V]

theorem finalBase_length {V : ℕ} (ps : List (Pass V)) (source target : ℕ) :
    CommonScanProgram.finalBase ps source target=
      if ps.length%2=0 then source else target := by
  induction ps generalizing source target with
  | nil => simp [CommonScanProgram.finalBase]
  | cons p ps ih =>
    rw [CommonScanProgram.finalBase,ih,List.length_cons]
    have hm : ps.length%2<2 := Nat.mod_lt _ (by omega)
    by_cases h : ps.length%2=0
    · have hn : (ps.length+1)%2≠0 := by omega
      simp only [if_pos h,if_neg hn]
    · have hn : (ps.length+1)%2=0 := by omega
      simp only [if_neg h,if_pos hn]

theorem padded_even {V : ℕ} (ps : List (Pass V)) : (padded ps).length%2=0 := by
  unfold padded
  split_ifs with h
  · exact h
  · simp only [List.length_append,List.length_singleton]
    omega

theorem destination_append {V : ℕ} (ps qs : List (Pass V)) :
    destination (ps++qs)=(destination ps).trans (destination qs) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [List.cons_append,destination,ih]; rfl

theorem padded_destination {V : ℕ} (ps : List (Pass V)) :
    destination (padded ps)=destination ps := by
  unfold padded
  split_ifs
  · rfl
  · rw [destination_append]
    apply Equiv.ext
    intro x
    rfl

theorem padded_constant {V : ℕ} (ps : List (Pass V)) :
    totalConstant (padded ps)≤totalConstant ps+8 := by
  unfold padded
  split_ifs
  · omega
  · simp [totalConstant,identityPass,Pass.constant]

def code (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source target : ℕ) : List (Instruction q) :=
  CommonScanProgram.code q reader (padded ps) source target

theorem safe (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source target : ℕ) :
    ∀ i∈code q reader ps source target,RespectsPC q i :=
  CommonScanProgram.code_safe q reader _ source target

theorem length_le (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source target : ℕ) :
    (code q reader ps source target).length≤3*(totalConstant ps+8)*count q V := by
  exact (CommonScanProgram.code_length q reader _ source target).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (padded_constant ps)))

theorem cost_le (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source target : ℕ) :
    cost q (code q reader ps source target)≤3*(totalConstant ps+8)*count q V := by
  exact (CommonScanProgram.code_cost q reader _ source target).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (padded_constant ps)))

theorem raw_correct (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source target : ℕ) (s : Machine q)
    (hs : source+count q V≤q.N^q.exponent)
    (ht : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source) (y : Fin V) :
    readBit q (executeRaw q (code q reader ps source target) s).1.disk source y.val=
      readBit q s.disk source ((destination ps).symm y).val := by
  have h := CommonScanProgram.raw_correct q reader (padded ps) source target s hs ht hsep y
  simpa only [code,finalBase_length,padded_even,if_pos,padded_destination] using h

theorem raw_outside (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source target : ℕ) (s : Machine q)
    (hs : source+count q V≤q.N^q.exponent)
    (ht : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source)
    (a : Fin (q.N^q.exponent))
    (has : a.val<source ∨ source+count q V≤a.val)
    (hat : a.val<target ∨ target+count q V≤a.val) :
    (executeRaw q (code q reader ps source target) s).1.disk a=s.disk a :=
  CommonScanProgram.raw_outside q reader (padded ps) source target s hs ht hsep a has hat

/-- The stream function appears only in the theorem, never in the code. -/
theorem raw_view (q : Configuration) {A : Type} {V : ℕ}
    (reader : Fin q.inventory.readers) (ps : List (Pass V))
    (layout : A ≃ Fin V) (perm : Equiv.Perm A)
    (hr : PhysicalRecursiveExchange.Realizes layout ps perm)
    (source target : ℕ) (s : Machine q)
    (hs : source+count q V≤q.N^q.exponent)
    (ht : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source)
    (F : A → Circuit.Bit)
    (hview : ∀ a,readBit q s.disk source (layout a).val=F a) :
    ∀ a,readBit q (executeRaw q (code q reader ps source target) s).1.disk
      source (layout a).val=Address.transport perm F a := by
  intro a
  rw [raw_correct q reader ps source target s hs ht hsep]
  have hi : (destination ps).symm (layout a)=layout (perm.symm a) := by
    apply (destination ps).injective
    rw [Equiv.apply_symm_apply,hr,Equiv.apply_symm_apply]
  rw [hi,hview]
  rfl
end
end CodedSorting.CommonRankEdgeScan
end RankEdgeScan

section RankEdge
/-! A matrix-edge program with actual child instruction fragments.
The child contracts are precisely the induction hypotheses for smaller
address fields; no oracle supplies outputs or a successful execution. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonRankEdge
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open RecursiveExchange RecursiveExchangeCost PhysicalRecursiveExchange
open CoordinateLayoutBridge Circuit Address CodedSimulation ScanProgram MatrixFactorization
attribute [local irreducible] CommonStaticSchedule.executeRaw
noncomputable section

structure Allocation (q : Configuration) (f P G S : ℕ) where
  source : ℕ
  buffer : ℕ
  limit : ℕ
  source_separate : source+count q (longVolume f P G S)≤buffer
  buffer_fits : buffer+count q (longVolume f P G S)≤limit
  fits : limit≤q.N^q.exponent

namespace Allocation
variable {q : Configuration} {f P G S : ℕ}
theorem source_fits (a : Allocation q f P G S) :
    a.source+count q (longVolume f P G S)≤q.N^q.exponent := by
  have := a.source_separate
  have := a.buffer_fits
  have := a.fits
  omega
theorem second_fits (a : Allocation q f P G S) :
    a.buffer+count q (longVolume f P G S)≤q.N^q.exponent := a.buffer_fits.trans a.fits
end Allocation

def View (q : Configuration) (f P G S : ℕ) (base : ℕ)
    (F : EdgeStream f P G S) (s : Machine q) : Prop :=
  ∀ a,readBit q s.disk base (commonLayout f P G S a).val=F a

/-- Recursive fragments transform the current source file in place.
All recursive scratch allocations lie between buffer and limit. -/
structure ChildProgram (q : Configuration) (f P G S : ℕ)
    (a : Allocation q f P G S) where
  instructions : Child → List (Instruction q)
  correct : ∀ c s F,View q f P G S a.source F s →
    View q f P G S a.source
      (transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) F)
      (executeRaw q (instructions c) s).1
  frame : ∀ c s (i : Fin (q.N^q.exponent)),
    (i.val < a.source ∨ a.source+count q (longVolume f P G S) ≤ i.val) →
    (i.val < a.buffer ∨ a.limit ≤ i.val) →
    (executeRaw q (instructions c) s).1.disk i=s.disk i
  safe : ∀ c i,i∈instructions c→RespectsPC q i

def scan (q : Configuration) (reader : Fin q.inventory.readers) (f P G S : ℕ)
    (a : Allocation q f P G S) (ps : List (Pass (longVolume f P G S))) :=
  CommonRankEdgeScan.code q reader ps a.source a.buffer

theorem scan_view (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (a : Allocation q f P G S)
    (ps : List (Pass (longVolume f P G S))) (perm : Equiv.Perm (EdgeAddress f P G S))
    (hr : Realizes (commonLayout f P G S) ps perm) (s : Machine q) (F : EdgeStream f P G S)
    (hv : View q f P G S a.source F s) :
    View q f P G S a.source (transport perm F) (executeRaw q (scan q reader f P G S a ps) s).1 :=
  CommonRankEdgeScan.raw_view q reader ps _ perm hr a.source a.buffer s
    a.source_fits a.second_fits (Or.inl a.source_separate) F hv

theorem scan_frame (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (a : Allocation q f P G S)
    (ps : List (Pass (longVolume f P G S))) (s : Machine q)
    (i : Fin (q.N^q.exponent))
    (hi : i.val < a.source ∨ a.source+count q (longVolume f P G S) ≤ i.val)
    (hw : i.val < a.buffer ∨ a.limit ≤ i.val) :
    (executeRaw q (scan q reader f P G S a ps) s).1.disk i=s.disk i := by
  apply CommonRankEdgeScan.raw_outside q reader ps a.source a.buffer s
    a.source_fits a.second_fits (Or.inl a.source_separate) i hi
  rcases hw with h|h
  · exact Or.inl h
  · exact Or.inr (a.buffer_fits.trans h)

def shortCode (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (c : Child) :=
  scan q reader f P G S a (scalarBefore f P G S c) ++ children.instructions c ++
    scan q reader f P G S a (scalarAfter f P G S c hS)

theorem short_view (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (c : Child) (s : Machine q) (F : EdgeStream f P G S)
    (hv : View q f P G S a.source F s) :
    View q f P G S a.source
      (transport (matrixLocation (unitEntry (Scalar f) (childRow c) (childCol c))) F)
      (executeRaw q (shortCode q reader f P G S hS a children c) s).1 := by
  let before : Equiv.Perm (EdgeAddress f P G S) := shortBefore f (childRow c) (childCol c)
  let exchange : Equiv.Perm (EdgeAddress f P G S) := SingleCoordinate.shortExchange (childRow c) (childCol c)
  let after : Equiv.Perm (EdgeAddress f P G S) := shortAfter f (childRow c) (childCol c)
  have h1 : ∀ t,View q f P G S a.source F t →
      View q f P G S a.source (transport before F)
      (executeRaw q (scan q reader f P G S a (scalarBefore f P G S c)) t).1 := by
    intro t ht
    exact scan_view q reader f P G S a _ before ((actualLayouts f P G S hG hS).shortBefore c) t F ht
  have h2 : ∀ t,View q f P G S a.source (transport before F) t →
      View q f P G S a.source (transport exchange (transport before F))
      (executeRaw q (children.instructions c) t).1 := by
    intro t ht
    exact children.correct c t _ ht
  have h3 : ∀ t,View q f P G S a.source (transport exchange (transport before F)) t →
      View q f P G S a.source (transport after (transport exchange (transport before F)))
      (executeRaw q (scan q reader f P G S a (scalarAfter f P G S c hS)) t).1 := by
    intro t ht
    exact scan_view q reader f P G S a _ after ((actualLayouts f P G S hG hS).shortAfter c) t _ ht
  have hh := CommonRawComposition.hoare_two q _ _ _ _ _
    (CommonRawComposition.hoare_two q _ _ _ _ _ h1 h2) h3 s hv
  have heq : transport after (transport exchange (transport before F))=
      transport (matrixLocation (unitEntry (Scalar f) (childRow c) (childCol c))) F := by
    rw [transport_comp,transport_comp]
    exact congrArg (fun e => transport e F) (short_comp f (childRow c) (childCol c))
  rw [heq] at hh
  exact hh

def sparseCode (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (e : Edge) (ps : List (EdgeChild e)) :=
  ps.flatMap (fun p => shortCode q reader f P G S hS a children ⟨e,p⟩)

def idealChild (f P G S : ℕ) (e : Edge) (p : EdgeChild e) :
    EdgeStream f P G S → EdgeStream f P G S :=
  transport (SingleCoordinate.shortExchange (oneRow p) (oneCol p))

theorem sparse_view (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (e : Edge) (ps : List (EdgeChild e))
    (s : Machine q) (F : EdgeStream f P G S) (hv : View q f P G S a.source F s) :
    View q f P G S a.source (sparseStreamProgram f e (idealChild f P G S e) ps F)
      (executeRaw q (sparseCode q reader f P G S hS a children e ps) s).1 := by
  induction ps generalizing s F with
  | nil => simpa only [sparseCode,List.flatMap_nil,executeRaw,sparseStreamProgram,List.foldl_nil] using hv
  | cons p ps ih =>
    have hh : ∀ t,View q f P G S a.source F t →
        View q f P G S a.source (shortStreamStep f e (idealChild f P G S e) p F)
        (executeRaw q (shortCode q reader f P G S hS a children ⟨e,p⟩) t).1 := by
      intro t ht
      rw [shortStreamStep_correct f e (idealChild f P G S e) (fun _ _ => rfl)]
      exact short_view q reader f P G S hG hS a children ⟨e,p⟩ t F ht
    exact CommonRawComposition.hoare_two q _ _ _ _ _ hh (fun t ht => ih t _ ht) s hv

def coreCode (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (e : Edge) :=
  scan q reader f P G S a (beforeProgram f P G S hG hS e) ++
    sparseCode q reader f P G S hS a children e (edgePivots e) ++
    scan q reader f P G S a (afterProgram f P G S hG hS e)

theorem core_view (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (e : Edge)
    (s : Machine q) (F : EdgeStream f P G S) (hv : View q f P G S a.source F s) :
    View q f P G S a.source (transport (matrixLocation (reducedEdgeMatrix f e)) F)
      (executeRaw q (coreCode q reader f P G S hG hS a children e) s).1 := by
  have h1 : ∀ t,View q f P G S a.source F t →
      View q f P G S a.source (transport (coordinatePermutation f e) F)
      (executeRaw q (scan q reader f P G S a (beforeProgram f P G S hG hS e)) t).1 := by
    intro t ht
    exact scan_view q reader f P G S a _ _ ((actualLayouts f P G S hG hS).before e) t F ht
  have h2 : ∀ t,View q f P G S a.source (transport (coordinatePermutation f e) F) t →
      View q f P G S a.source
      (sparseStreamProgram f e (idealChild f P G S e) (edgePivots e) (transport (coordinatePermutation f e) F))
      (executeRaw q (sparseCode q reader f P G S hS a children e (edgePivots e)) t).1 := by
    intro t ht
    exact sparse_view q reader f P G S hG hS a children e _ t _ ht
  have h3 : ∀ t,View q f P G S a.source
      (sparseStreamProgram f e (idealChild f P G S e) (edgePivots e) (transport (coordinatePermutation f e) F)) t →
      View q f P G S a.source (edgeStreamProgram f e (idealChild f P G S e) F)
      (executeRaw q (scan q reader f P G S a (afterProgram f P G S hG hS e)) t).1 := by
    intro t ht
    exact scan_view q reader f P G S a _ _ ((actualLayouts f P G S hG hS).after e) t _ ht
  have hh := CommonRawComposition.hoare_two q _ _ _ _ _
    (CommonRawComposition.hoare_two q _ _ _ _ _ h1 h2) h3 s hv
  rw [edgeStreamProgram_correct f e (idealChild f P G S e) (fun _ _ => rfl)] at hh
  exact hh
end
end CodedSorting.CommonRankEdge
end RankEdge

section RankEdgeResources
/-! Frame, program-counter safety, and charged rank-indexed calls for the
actual factorized matrix-edge program. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonRankEdge
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open RecursiveExchange RecursiveExchangeCost PhysicalRecursiveExchange
open CoordinateLayoutBridge Circuit Address CodedSimulation ScanProgram
attribute [local irreducible] CommonStaticSchedule.executeRaw
noncomputable section

theorem short_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (c : Child) :
    ∀ i∈shortCode q reader f P G S hS a children c,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · rcases List.mem_append.mp hi with hi|hi
    · exact CommonRankEdgeScan.safe q reader _ _ _ i hi
    · exact children.safe c i hi
  · exact CommonRankEdgeScan.safe q reader _ _ _ i hi

theorem sparse_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (e : Edge) (ps : List (EdgeChild e)) :
    ∀ i∈sparseCode q reader f P G S hS a children e ps,RespectsPC q i := by
  intro i hi
  obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp hi
  exact short_safe q reader f P G S hS a children ⟨e,p⟩ i hp

theorem core_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (e : Edge) :
    ∀ i∈coreCode q reader f P G S hG hS a children e,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · rcases List.mem_append.mp hi with hi|hi
    · exact CommonRankEdgeScan.safe q reader _ _ _ i hi
    · exact sparse_safe q reader f P G S hS a children e _ i hi
  · exact CommonRankEdgeScan.safe q reader _ _ _ i hi

theorem short_frame (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (c : Child) (s : Machine q)
    (i : Fin (q.N^q.exponent))
    (hi : i.val < a.source ∨ a.source+count q (longVolume f P G S) ≤ i.val)
    (hw : i.val < a.buffer ∨ a.limit ≤ i.val) :
    (executeRaw q (shortCode q reader f P G S hS a children c) s).1.disk i=s.disk i := by
  rw [shortCode,raw_append,raw_append,scan_frame q reader f P G S a _ _ i hi hw,
    children.frame c _ i hi hw,scan_frame q reader f P G S a _ _ i hi hw]

theorem sparse_frame (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (e : Edge) (ps : List (EdgeChild e))
    (s : Machine q) (i : Fin (q.N^q.exponent))
    (hi : i.val < a.source ∨ a.source+count q (longVolume f P G S) ≤ i.val)
    (hw : i.val < a.buffer ∨ a.limit ≤ i.val) :
    (executeRaw q (sparseCode q reader f P G S hS a children e ps) s).1.disk i=s.disk i := by
  induction ps generalizing s with
  | nil => simp only [sparseCode,List.flatMap_nil,executeRaw]
  | cons p ps ih =>
    change (executeRaw q (shortCode q reader f P G S hS a children ⟨e,p⟩ ++
      sparseCode q reader f P G S hS a children e ps) s).1.disk i=_
    rw [raw_append,ih,short_frame q reader f P G S hS a children ⟨e,p⟩ s i hi hw]

theorem core_frame (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (e : Edge) (s : Machine q)
    (i : Fin (q.N^q.exponent))
    (hi : i.val < a.source ∨ a.source+count q (longVolume f P G S) ≤ i.val)
    (hw : i.val < a.buffer ∨ a.limit ≤ i.val) :
    (executeRaw q (coreCode q reader f P G S hG hS a children e) s).1.disk i=s.disk i := by
  rw [coreCode,raw_append,raw_append,scan_frame q reader f P G S a _ _ i hi hw,
    sparse_frame q reader f P G S hS a children e _ _ i hi hw,
    scan_frame q reader f P G S a _ _ i hi hw]

def localCharge (q : Configuration) (f P G S : ℕ) (hG : 0<G) (hS : 0<S) (e : Edge) : ℕ :=
  3*(totalConstant (beforeProgram f P G S hG hS e)+
    totalConstant (afterProgram f P G S hG hS e)+16)*count q (longVolume f P G S)+
    138*(edgePivots e).length*count q (longVolume f P G S)

def childSum (e : Edge) (charge : Child→ℕ) : ℕ :=
  ((edgePivots e).map (fun p => charge ⟨e,p⟩)).sum

theorem short_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (c : Child) :
    (shortCode q reader f P G S hS a children c).length≤
      138*count q (longVolume f P G S)+(children.instructions c).length := by
  have hb := CommonRankEdgeScan.length_le q reader (scalarBefore f P G S c) a.source a.buffer
  have ha := CommonRankEdgeScan.length_le q reader (scalarAfter f P G S c hS) a.source a.buffer
  rw [scalarBefore_constant] at hb
  rw [scalarAfter_constant] at ha
  simp only [shortCode,List.length_append,scan]
  omega

theorem short_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (c : Child) :
    cost q (shortCode q reader f P G S hS a children c)≤
      138*count q (longVolume f P G S)+cost q (children.instructions c) := by
  have hb := CommonRankEdgeScan.cost_le q reader (scalarBefore f P G S c) a.source a.buffer
  have ha := CommonRankEdgeScan.cost_le q reader (scalarAfter f P G S c hS) a.source a.buffer
  rw [scalarBefore_constant] at hb
  rw [scalarAfter_constant] at ha
  simp only [shortCode,cost_append,scan]
  omega

theorem sparse_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (e : Edge) (ps : List (EdgeChild e)) :
    (sparseCode q reader f P G S hS a children e ps).length≤
      138*ps.length*count q (longVolume f P G S)+
        (ps.map (fun p => (children.instructions ⟨e,p⟩).length)).sum := by
  induction ps with
  | nil => simp [sparseCode]
  | cons p ps ih =>
    have hh := short_length q reader f P G S hS a children ⟨e,p⟩
    change (_++sparseCode q reader f P G S hS a children e ps).length≤_
    simp only [List.length_append,List.length_cons,List.map_cons,List.sum_cons]
    nlinarith

theorem sparse_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (e : Edge) (ps : List (EdgeChild e)) :
    cost q (sparseCode q reader f P G S hS a children e ps)≤
      138*ps.length*count q (longVolume f P G S)+
        (ps.map (fun p => cost q (children.instructions ⟨e,p⟩))).sum := by
  induction ps with
  | nil => simp [sparseCode,cost]
  | cons p ps ih =>
    have hh := short_cost q reader f P G S hS a children ⟨e,p⟩
    change cost q (_++sparseCode q reader f P G S hS a children e ps)≤_
    simp only [cost_append,List.length_cons,List.map_cons,List.sum_cons]
    nlinarith

theorem core_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (e : Edge) :
    (coreCode q reader f P G S hG hS a children e).length≤
      localCharge q f P G S hG hS e+childSum e (fun c => (children.instructions c).length) := by
  have hb := CommonRankEdgeScan.length_le q reader (beforeProgram f P G S hG hS e) a.source a.buffer
  have ha := CommonRankEdgeScan.length_le q reader (afterProgram f P G S hG hS e) a.source a.buffer
  have hm := sparse_length q reader f P G S hS a children e (edgePivots e)
  simp only [coreCode,List.length_append,scan,localCharge,childSum]
  nlinarith

theorem core_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S) (a : Allocation q f P G S)
    (children : ChildProgram q f P G S a) (e : Edge) :
    cost q (coreCode q reader f P G S hG hS a children e)≤
      localCharge q f P G S hG hS e+childSum e (fun c => cost q (children.instructions c)) := by
  have hb := CommonRankEdgeScan.cost_le q reader (beforeProgram f P G S hG hS e) a.source a.buffer
  have ha := CommonRankEdgeScan.cost_le q reader (afterProgram f P G S hG hS e) a.source a.buffer
  have hm := sparse_cost q reader f P G S hS a children e (edgePivots e)
  simp only [coreCode,cost_append,scan,localCharge,childSum]
  nlinarith

/-- The actual emitted child list has exactly the rank-derived count. -/
theorem invocation_count (e : Edge) : (edgePivots e).length=(edgeMatrix e).rank := by
  exact edgePivots_length e
end
end CodedSorting.CommonRankEdge
end RankEdgeResources

section RankEdgeNetwork
/-! Instantiation of the arbitrary-width network edge interface by real
rank-factor scans, child programs, and one charged final output copy. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
namespace CodedSorting.CommonRankEdge
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open RecursiveExchange RecursiveExchangeCost PhysicalRecursiveExchange
open CoordinateLayoutBridge Circuit Address CodedSimulation ScanProgram
open CommonResidentNetwork
attribute [local irreducible] CommonStaticSchedule.executeRaw
noncomputable section

theorem file_before_child (q : Configuration) (f P G S : ℕ)
    (p : CommonRecursiveNetwork.Layout q f P G S) (file : CommonResidentNetwork.File) :
    base p.workspace p.stride file+count q (longVolume f P G S)≤p.childBase := by
  have h := Nat.mul_le_mul_right p.stride (Nat.succ_le_of_lt (slot_lt file))
  have hc := p.count_le_stride
  have hn := p.network_le_child
  dsimp only [base]
  nlinarith

def networkAllocation (q : Configuration) (f P G S : ℕ)
    (p : CommonRecursiveNetwork.Layout q f P G S)
    (hbuffer : p.childBase+count q (longVolume f P G S)≤p.childLimit) :
    Allocation q f P G S where
  source := scratchBase p.workspace p.stride
  buffer := p.childBase
  limit := p.childLimit
  source_separate := file_before_child q f P G S p (.inr (.inr ()))
  buffer_fits := hbuffer
  fits := p.fit

def copyCode (q : Configuration) (reader : Fin q.inventory.readers) (V source target : ℕ) :=
  CommonPermutationScan.program q reader (Equiv.refl (Fin V)) (fun _ => (0 : Fin 1)) source target

def networkInstructions (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S)
    (p : CommonRecursiveNetwork.Layout q f P G S)
    (hbuffer : p.childBase+count q (longVolume f P G S)≤p.childLimit)
    (children : ChildProgram q f P G S (networkAllocation q f P G S p hbuffer)) (e : Edge) :=
  coreCode q reader f P G S hG hS (networkAllocation q f P G S p hbuffer) children e ++
    copyCode q reader (longVolume f P G S) (scratchBase p.workspace p.stride)
      (edgeBase p.workspace p.stride e)

theorem copy_fit_separate (q : Configuration) (f P G S : ℕ)
    (p : CommonRecursiveNetwork.Layout q f P G S) (e : Edge) :
    scratchBase p.workspace p.stride+count q (longVolume f P G S)≤q.N^q.exponent ∧
    edgeBase p.workspace p.stride e+count q (longVolume f P G S)≤q.N^q.exponent ∧
    (scratchBase p.workspace p.stride+count q (longVolume f P G S)≤edgeBase p.workspace p.stride e ∨
    edgeBase p.workspace p.stride e+count q (longVolume f P G S)≤scratchBase p.workspace p.stride) := by
  have hs := (file_before_child q f P G S p (.inr (.inr ()))).trans (p.child_le_limit.trans p.fit)
  have ht := (file_before_child q f P G S p (.inr (.inl e))).trans (p.child_le_limit.trans p.fit)
  refine ⟨hs,ht,?_⟩
  have hh := base_separate p.workspace p.stride (.inr (.inr ())) (.inr (.inl e)) (by simp)
  rcases hh with hh|hh
  · exact Or.inl ((Nat.add_le_add_left p.count_le_stride _).trans hh)
  · exact Or.inr ((Nat.add_le_add_left p.count_le_stride _).trans hh)

def networkEdgePrograms (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S)
    (p : CommonRecursiveNetwork.Layout q f P G S)
    (hbuffer : p.childBase+count q (longVolume f P G S)≤p.childLimit)
    (children : ChildProgram q f P G S (networkAllocation q f P G S p hbuffer)) :
    CommonRecursiveNetwork.EdgeProgram q f P G S p where
  instructions := networkInstructions q reader f P G S hG hS p hbuffer children
  correct e s F hv := by
    obtain ⟨hs,ht,hsep⟩ := copy_fit_separate q f P G S p e
    let result := transport (matrixLocation (reducedEdgeMatrix f e)) F
    have h1 : ∀ t,View q f P G S (scratchBase p.workspace p.stride) F t →
        View q f P G S (scratchBase p.workspace p.stride) result
        (executeRaw q (coreCode q reader f P G S hG hS (networkAllocation q f P G S p hbuffer) children e) t).1 := by
      intro t ht
      exact core_view q reader f P G S hG hS _ children e t F ht
    have h2 : ∀ t,View q f P G S (scratchBase p.workspace p.stride) result t →
        View q f P G S (edgeBase p.workspace p.stride e) result
        (executeRaw q (copyCode q reader (longVolume f P G S) (scratchBase p.workspace p.stride)
          (edgeBase p.workspace p.stride e)) t).1 := by
      intro t hv a
      exact ((CommonPermutationScan.raw_correct q reader (Equiv.refl _) (fun _ => (0 : Fin 1))
        _ _ hs ht hsep t).1 (commonLayout f P G S a)).trans (hv a)
    exact CommonRawComposition.hoare_two q _ _ _ _ _ h1 h2 s hv
  frame e s i hi ht hw := by
    obtain ⟨hs,hfit,hsep⟩ := copy_fit_separate q f P G S p e
    have hi' : i.val < scratchBase p.workspace p.stride ∨
        scratchBase p.workspace p.stride+count q (longVolume f P G S) ≤ i.val := by
      rcases hi with hi|hi
      · exact Or.inl hi
      · exact Or.inr ((Nat.add_le_add_left p.count_le_stride _).trans hi)
    have ht' : i.val < edgeBase p.workspace p.stride e ∨
        edgeBase p.workspace p.stride e+count q (longVolume f P G S) ≤ i.val := by
      rcases ht with ht|ht
      · exact Or.inl ht
      · exact Or.inr ((Nat.add_le_add_left p.count_le_stride _).trans ht)
    rw [networkInstructions,raw_append]
    unfold copyCode
    rw [(CommonPermutationScan.raw_correct q reader (Equiv.refl _) (fun _ => (0 : Fin 1))
      _ _ hs hfit hsep _).2 i ht']
    exact core_frame q reader f P G S hG hS _ children e s i hi' hw
  safe e i hi := by
    rcases List.mem_append.mp hi with hi|hi
    · exact core_safe q reader f P G S hG hS _ children e i hi
    · exact CommonPermutationScan.program_safe q reader _ _ _ _ i hi

theorem network_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S)
    (p : CommonRecursiveNetwork.Layout q f P G S)
    (hbuffer : p.childBase+count q (longVolume f P G S)≤p.childLimit)
    (children : ChildProgram q f P G S (networkAllocation q f P G S p hbuffer)) (e : Edge) :
    ((networkEdgePrograms q reader f P G S hG hS p hbuffer children).instructions e).length≤
      localCharge q f P G S hG hS e+6*count q (longVolume f P G S)+
        childSum e (fun c => (children.instructions c).length) := by
  have hc := core_length q reader f P G S hG hS _ children e
  have hh := CommonPermutationScan.program_length q reader (Equiv.refl (Fin (longVolume f P G S)))
    (fun _ => (0 : Fin 1)) (scratchBase p.workspace p.stride) (edgeBase p.workspace p.stride e)
    (by intro x y h _; exact h)
  change (_++copyCode q reader _ _ _).length≤_
  rw [List.length_append]
  dsimp only [copyCode]
  omega

theorem network_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S)
    (p : CommonRecursiveNetwork.Layout q f P G S)
    (hbuffer : p.childBase+count q (longVolume f P G S)≤p.childLimit)
    (children : ChildProgram q f P G S (networkAllocation q f P G S p hbuffer)) (e : Edge) :
    cost q ((networkEdgePrograms q reader f P G S hG hS p hbuffer children).instructions e)≤
      localCharge q f P G S hG hS e+6*count q (longVolume f P G S)+
        childSum e (fun c => cost q (children.instructions c)) := by
  have hc := core_cost q reader f P G S hG hS _ children e
  have hh := CommonPermutationScan.program_cost q reader (Equiv.refl (Fin (longVolume f P G S)))
    (fun _ => (0 : Fin 1)) (scratchBase p.workspace p.stride) (edgeBase p.workspace p.stride e)
    (by intro x y h _; exact h)
  change cost q (_++copyCode q reader _ _ _)≤_
  rw [cost_append]
  dsimp only [copyCode]
  omega
end
end CodedSorting.CommonRankEdge
end RankEdgeNetwork

section RankEdgeSum
/-! The finite network uses exactly S child calls, each already present in
its instruction list. All nonrecursive scans have a width-independent
construction constant. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonRankEdge
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open RecursiveExchange RecursiveExchangeCost PhysicalRecursiveExchange
open PhysicalRecursiveCost Circuit ScanProgram
open scoped BigOperators
noncomputable section

theorem childSum_eq (e : Edge) (charge : Child→ℕ) :
    childSum e charge=∑ p : EdgeChild e,charge ⟨e,p⟩ := by
  simp only [childSum,edgePivots,Finset.sum_map_toList]

theorem childSum_total (charge : Child→ℕ) :
    (∑ e : Edge,childSum e charge)=∑ c : Child,charge c := by
  simp_rw [childSum_eq]
  exact (Fintype.sum_sigma charge).symm

theorem childSum_total_uniform (charge : Child→ℕ) (C : ℕ) (h : ∀ c,charge c≤C) :
    (∑ e : Edge,childSum e charge)≤Parameters.S*C := by
  rw [childSum_total]
  calc
    _ ≤ ∑ _ : Child,C := Finset.sum_le_sum (fun c _ => h c)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,child_count]

def edgeScanConstant (e : Edge) : ℕ :=
  3*(beforeConstant e+afterConstant e+16)+138*(edgeMatrix e).rank+6

def constructionConstant : ℕ := ∑ e : Edge,edgeScanConstant e

theorem localCharge_bound (q : Configuration) (f P G S : ℕ)
    (hG : 0<G) (hS : 0<S) (e : Edge) :
    localCharge q f P G S hG hS e+6*count q (longVolume f P G S)≤
      edgeScanConstant e*count q (longVolume f P G S) := by
  have hb := beforeProgram_constant f P G S hG hS e
  have ha := afterProgram_constant f P G S hG hS e
  have hh := Nat.mul_le_mul_right (count q (longVolume f P G S)) (Nat.add_le_add hb ha)
  unfold localCharge edgeScanConstant
  rw [edgePivots_length]
  nlinarith

theorem localCharge_total (q : Configuration) (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :
    (∑ e : Edge,(localCharge q f P G S hG hS e+6*count q (longVolume f P G S)))≤
      constructionConstant*count q (longVolume f P G S) := by
  unfold constructionConstant
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun e _ => localCharge_bound q f P G S hG hS e)

theorem network_cost_total (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S)
    (p : CommonRecursiveNetwork.Layout q f P G S)
    (hbuffer : p.childBase+count q (longVolume f P G S)≤p.childLimit)
    (children : ChildProgram q f P G S (networkAllocation q f P G S p hbuffer)) :
    (∑ e : Edge,cost q ((networkEdgePrograms q reader f P G S hG hS p hbuffer children).instructions e))≤
      constructionConstant*count q (longVolume f P G S)+∑ c : Child,cost q (children.instructions c) := by
  calc
    _ ≤ ∑ e : Edge,(localCharge q f P G S hG hS e+6*count q (longVolume f P G S)+
          childSum e (fun c => cost q (children.instructions c))) :=
      Finset.sum_le_sum (fun e _ => network_cost q reader f P G S hG hS p hbuffer children e)
    _ = (∑ e : Edge,(localCharge q f P G S hG hS e+6*count q (longVolume f P G S)))+
          ∑ c : Child,cost q (children.instructions c) := by
      rw [Finset.sum_add_distrib,childSum_total]
    _ ≤ _ := Nat.add_le_add_right (localCharge_total q f P G S hG hS) _

theorem network_length_total (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S)
    (p : CommonRecursiveNetwork.Layout q f P G S)
    (hbuffer : p.childBase+count q (longVolume f P G S)≤p.childLimit)
    (children : ChildProgram q f P G S (networkAllocation q f P G S p hbuffer)) :
    (∑ e : Edge,((networkEdgePrograms q reader f P G S hG hS p hbuffer children).instructions e).length)≤
      constructionConstant*count q (longVolume f P G S)+∑ c : Child,(children.instructions c).length := by
  calc
    _ ≤ ∑ e : Edge,(localCharge q f P G S hG hS e+6*count q (longVolume f P G S)+
          childSum e (fun c => (children.instructions c).length)) :=
      Finset.sum_le_sum (fun e _ => network_length q reader f P G S hG hS p hbuffer children e)
    _ = (∑ e : Edge,(localCharge q f P G S hG hS e+6*count q (longVolume f P G S)))+
          ∑ c : Child,(children.instructions c).length := by
      rw [Finset.sum_add_distrib,childSum_total]
    _ ≤ _ := Nat.add_le_add_right (localCharge_total q f P G S hG hS) _
end
end CodedSorting.CommonRankEdge
end RankEdgeSum
