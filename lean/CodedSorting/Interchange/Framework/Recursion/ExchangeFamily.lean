import CodedSorting.Circuit.NetworkModel.Framework.RankEdgeSum
import CodedSorting.Interchange.Framework.Recursion.NetworkCost
import CodedSorting.Interchange.Framework.Recursion.RecursiveCallShape
import CodedSorting.Interchange.Framework.Recursion.OuterCopyFrame

section ExchangeCost
/-! A compositional bound for the actual recursive network. The supplied
child charges bound concrete child instruction lists; their costs occur
once for each rank-selected invocation, with all surrounding scans charged. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonRecursiveExchangeCost
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open RecursiveExchange RecursiveExchangeCost PhysicalRecursiveExchange
open CommonResidentNetwork
noncomputable section
attribute [local irreducible] CommonResidentNetwork.edgeCount CircuitProgram.globalProgram Parameters.W

def networkCharge (q : Configuration) (f P G S : ℕ) (hG : 0<G) (hS : 0<S)
    (childCharge : Child→ℕ) : ℕ :=
  3*prefixWeight edgeCount le_rfl*count q (longVolume f P G S)+
    CommonRecursiveNetwork.edgeSum (fun e =>
      CommonRankEdge.localCharge q f P G S hG hS e+6*count q (longVolume f P G S)+
        CommonRankEdge.childSum e childCharge)

theorem childSum_mono (e : Edge) (value bound : Child→ℕ)
    (h : ∀ c,value c≤bound c) : CommonRankEdge.childSum e value≤CommonRankEdge.childSum e bound := by
  unfold CommonRankEdge.childSum
  apply List.sum_le_sum
  intro i hi
  exact h _

theorem network_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S)
    (p : CommonRecursiveNetwork.Layout q f P G S)
    (hbuffer : p.childBase+count q (longVolume f P G S)≤p.childLimit)
    (children : CommonRankEdge.ChildProgram q f P G S
      (CommonRankEdge.networkAllocation q f P G S p hbuffer))
    (childCharge : Child→ℕ)
    (hchild : ∀ c,cost q (children.instructions c)≤childCharge c) :
    cost q (CommonRecursiveNetwork.code q reader f P G S p
      (CommonRankEdge.networkEdgePrograms q reader f P G S hG hS p hbuffer children))≤
      networkCharge q f P G S hG hS childCharge := by
  rw [CommonRecursiveNetwork.code_cost]
  unfold networkCharge
  apply Nat.add_le_add_left
  apply CommonRecursiveNetwork.edgeSum_mono
  intro e
  exact (CommonRankEdge.network_cost q reader f P G S hG hS p hbuffer children e).trans
    (Nat.add_le_add_left (childSum_mono e _ _ hchild) _)

theorem network_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S)
    (p : CommonRecursiveNetwork.Layout q f P G S)
    (hbuffer : p.childBase+count q (longVolume f P G S)≤p.childLimit)
    (children : CommonRankEdge.ChildProgram q f P G S
      (CommonRankEdge.networkAllocation q f P G S p hbuffer))
    (childCharge : Child→ℕ)
    (hchild : ∀ c,(children.instructions c).length≤childCharge c) :
    (CommonRecursiveNetwork.code q reader f P G S p
      (CommonRankEdge.networkEdgePrograms q reader f P G S hG hS p hbuffer children)).length≤
      networkCharge q f P G S hG hS childCharge := by
  rw [CommonRecursiveNetwork.code_length]
  unfold networkCharge
  apply Nat.add_le_add_left
  apply CommonRecursiveNetwork.edgeSum_mono
  intro e
  exact (CommonRankEdge.network_length q reader f P G S hG hS p hbuffer children e).trans
    (Nat.add_le_add_left (childSum_mono e _ _ hchild) _)

end
end CodedSorting.CommonRecursiveExchangeCost
end ExchangeCost

section PhysicalRecursiveAdapters
/-! Address-preserving adapters between the actual scalar recursive files
and the common file codec used by a whole network level. None executes a
permutation or reads an external file. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 600000
namespace CodedSorting.PhysicalRecursiveAdapters
open Circuit Address RecursiveExchange RecursiveExchangeCost
open PhysicalRecursiveExchange PhysicalFieldPacking CoordinateLayoutBridge ScalarLayoutBridge
noncomputable section

/-- Changing only the finite type's cardinality proof does not alter a file. -/
theorem represented_cast {A : Type} {V U : ℕ} (layout : A ≃ Fin V) (h : V=U)
    (B : ℕ) (hB : 0 < B) (F : A → Bit) :
    represented (layout.trans (finCongr h)) B hB F=represented layout B hB F := by
  subst U
  rfl

theorem regroup_exchange_file {A D : Type} {V U : ℕ}
    (layout : A ≃ Fin V) (other : D ≃ Fin U) (h : U=V) (shape : A ≃ D)
    (haddr : ∀ a,finCongr h (other (shape a))=layout a)
    (B : ℕ) (hB : 0 < B) (F : A → Bit) (op : (D → Bit) → D → Bit) :
    represented other B hB (op (F ∘ shape.symm)) =
      represented layout B hB (viaShape shape op F) := by
  rw [← represented_cast other h]
  have hfun : (viaShape shape op F) ∘ shape.symm = op (F ∘ shape.symm) := by
    funext a
    simp only [Function.comp_apply,viaShape,Equiv.apply_symm_apply]
    rfl
  rw [← hfun]
  exact represented_regroup layout (other.trans (finCongr h)) shape haddr B hB _

def childScalarShape (f P G S : ℕ) (c : Child) :
    EdgeAddress f P G S ≃
      FullAddress (Fin (childP f P c)) (Scalar f) (Fin (childG f G c)) (Fin (childS f S c)) :=
  (childRepack f c).trans
    (addressShape (prefixCode f P c) (Equiv.refl _) (gapCode f G c) (suffixCode f S c))

theorem child_scalar_address (f P G S : ℕ) (c : Child) (a : EdgeAddress f P G S) :
    finCongr (child_volume f P G S c)
      (scalarLayout f (childP f P c) (childG f G c) (childS f S c) (childScalarShape f P G S c a)) =
      commonLayout f P G S a := by
  exact child_common f P G S c a

theorem child_scalar_file (f P G S B : ℕ) (hB : 0 < B) (c : Child)
    (F : EdgeAddress f P G S → Bit) :
    represented (scalarLayout f (childP f P c) (childG f G c) (childS f S c)) B hB
      (F ∘ (childScalarShape f P G S c).symm) =
        represented (commonLayout f P G S) B hB F := by
  rw [← represented_cast _ (child_volume f P G S c)]
  exact represented_regroup _ _ _ (child_scalar_address f P G S c) B hB F

theorem child_scalar_exchange (f P G S : ℕ) (c : Child)
    (F : EdgeAddress f P G S → Bit) :
    viaShape (childScalarShape f P G S c) (transport exchangeEquiv) F =
      transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) F := by
  have h := viaShape_exchange (prefixCode f P c) (Equiv.refl (Scalar f))
    (gapCode f G c) (suffixCode f S c) (F ∘ (childRepack f c).symm)
  calc
    _ = viaShape (childRepack f c)
      (viaShape (addressShape (prefixCode f P c) (Equiv.refl (Scalar f))
        (gapCode f G c) (suffixCode f S c)) (transport exchangeEquiv)) F := rfl
    _ = viaShape (childRepack f c) (transport exchangeEquiv) F := by
      unfold viaShape
      funext a
      exact congrFun h ((childRepack f c) a)
    _ = _ := viaShape_shortExchange f c F

theorem child_scalar_output_file (f P G S B : ℕ) (hB : 0 < B) (c : Child)
    (F : EdgeAddress f P G S → Bit) :
    represented (scalarLayout f (childP f P c) (childG f G c) (childS f S c)) B hB
      (transport exchangeEquiv (F ∘ (childScalarShape f P G S c).symm)) =
    represented (commonLayout f P G S) B hB
      (transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) F) := by
  rw [regroup_exchange_file _ _ (child_volume f P G S c) _
    (child_scalar_address f P G S c),child_scalar_exchange]

def scalarPrefixShape (f P Q G S : ℕ) (h : P=Q) :
    FullAddress (Fin P) (Scalar f) (Fin G) (Fin S) ≃
      FullAddress (Fin Q) (Scalar f) (Fin G) (Fin S) :=
  addressShape (finCongr h) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

theorem scalar_prefix_file (f P Q G S B : ℕ) (hB : 0 < B) (h : P=Q)
    (F : FullAddress (Fin P) (Scalar f) (Fin G) (Fin S) → Bit) :
    represented (scalarLayout f Q G S) B hB (F ∘ (scalarPrefixShape f P Q G S h).symm) =
      represented (scalarLayout f P G S) B hB F := by
  subst Q
  rfl

theorem scalar_prefix_output_file (f P Q G S B : ℕ) (hB : 0 < B) (h : P=Q)
    (F : FullAddress (Fin P) (Scalar f) (Fin G) (Fin S) → Bit) :
    represented (scalarLayout f Q G S) B hB
      (transport exchangeEquiv (F ∘ (scalarPrefixShape f P Q G S h).symm)) =
      represented (scalarLayout f P G S) B hB (transport exchangeEquiv F) := by
  subst Q
  rfl


def scalarCastShape (f f' P P' G S : ℕ) (hf : f=f') (hp : P=P') :
    FullAddress (Fin P) (Scalar f) (Fin G) (Fin S) ≃
      FullAddress (Fin P') (Scalar f') (Fin G) (Fin S) :=
  addressShape (finCongr hp) (Equiv.cast (congrArg Scalar hf)) (Equiv.refl _) (Equiv.refl _)

theorem scalar_cast_file (f f' P P' G S B : ℕ) (hB : 0 < B) (hf : f=f') (hp : P=P')
    (F : FullAddress (Fin P) (Scalar f) (Fin G) (Fin S) → Bit) :
    represented (scalarLayout f' P' G S) B hB (F ∘ (scalarCastShape f f' P P' G S hf hp).symm) =
      represented (scalarLayout f P G S) B hB F := by
  subst f'
  subst P'
  rfl

theorem scalar_cast_output_file (f f' P P' G S B : ℕ) (hB : 0 < B) (hf : f=f') (hp : P=P')
    (F : FullAddress (Fin P) (Scalar f) (Fin G) (Fin S) → Bit) :
    represented (scalarLayout f' P' G S) B hB
      (transport exchangeEquiv (F ∘ (scalarCastShape f f' P P' G S hf hp).symm)) =
      represented (scalarLayout f P G S) B hB (transport exchangeEquiv F) := by
  subst f'
  subst P'
  rfl

def packedShape (f P G S : ℕ) : EdgeAddress f P G S ≃
    FullAddress (Fin P) (Scalar (Parameters.m*f)) (Fin G) (Fin S) :=
  addressShape (Equiv.refl _) (blockPacking f) (Equiv.refl _) (Equiv.refl _)

theorem packed_file (f P G S B : ℕ) (hB : 0 < B)
    (F : FullAddress (Fin P) (Scalar (Parameters.m*f)) (Fin G) (Fin S) → Bit) :
    represented (commonLayout f P G S) B hB (F ∘ packedShape f P G S) =
      represented (scalarLayout (Parameters.m*f) P G S) B hB F := by
  have h := blockPacking_same_file f P G S B hB (F ∘ packedShape f P G S)
  rw [represented_cast] at h
  have he : (F ∘ packedShape f P G S) ∘ (packedShape f P G S).symm=F := by
    funext a
    simp only [Function.comp_apply,Equiv.apply_symm_apply]
  change represented (scalarLayout (Parameters.m*f) P G S) B hB
    ((F ∘ packedShape f P G S) ∘ (packedShape f P G S).symm) = _ at h
  rw [he] at h
  exact h.symm

theorem packed_output_file (f P G S B : ℕ) (hB : 0 < B)
    (F : FullAddress (Fin P) (Scalar (Parameters.m*f)) (Fin G) (Fin S) → Bit) :
    represented (commonLayout f P G S) B hB (transport exchangeEquiv (F ∘ packedShape f P G S)) =
      represented (scalarLayout (Parameters.m*f) P G S) B hB (transport exchangeEquiv F) := by
  have he : transport exchangeEquiv (F ∘ packedShape f P G S) =
      (transport exchangeEquiv F) ∘ packedShape f P G S := rfl
  rw [he,packed_file]

theorem parent_width (base k : ℕ) :
    base*Parameters.m^(k+1)=Parameters.m*(base*Parameters.m^k) := by
  rw [pow_succ]
  ring

theorem parent_prefix (rows k : ℕ) :
    rows*Parameters.W^(k+1)=(rows*Parameters.W^k)*Parameters.W := by
  rw [pow_succ,Nat.mul_assoc]

def parentData (base k rows G S : ℕ)
    (F : FullAddress (Fin (rows*Parameters.W^(k+1)))
      (Scalar (base*Parameters.m^(k+1))) (Fin G) (Fin S) → Bit) :
    EdgeStream (base*Parameters.m^k) ((rows*Parameters.W^k)*Parameters.W) G S :=
  (F ∘ (scalarCastShape _ _ _ _ G S (parent_width base k) (parent_prefix rows k)).symm) ∘
    packedShape (base*Parameters.m^k) ((rows*Parameters.W^k)*Parameters.W) G S

theorem parent_file (base k rows G S B : ℕ) (hB : 0 < B)
    (F : FullAddress (Fin (rows*Parameters.W^(k+1)))
      (Scalar (base*Parameters.m^(k+1))) (Fin G) (Fin S) → Bit) :
    represented (commonLayout (base*Parameters.m^k) ((rows*Parameters.W^k)*Parameters.W) G S)
      B hB (parentData base k rows G S F) =
    represented (scalarLayout (base*Parameters.m^(k+1)) (rows*Parameters.W^(k+1)) G S) B hB F := by
  rw [parentData,packed_file,scalar_cast_file]

theorem parent_output_file (base k rows G S B : ℕ) (hB : 0 < B)
    (F : FullAddress (Fin (rows*Parameters.W^(k+1)))
      (Scalar (base*Parameters.m^(k+1))) (Fin G) (Fin S) → Bit) :
    represented (commonLayout (base*Parameters.m^k) ((rows*Parameters.W^k)*Parameters.W) G S)
      B hB (transport exchangeEquiv (parentData base k rows G S F)) =
    represented (scalarLayout (base*Parameters.m^(k+1)) (rows*Parameters.W^(k+1)) G S)
      B hB (transport exchangeEquiv F) := by
  rw [parentData,packed_output_file,scalar_cast_output_file]

theorem parent_volume (base k rows G S : ℕ) :
    longVolume (base*Parameters.m^k) ((rows*Parameters.W^k)*Parameters.W) G S =
      ScalarVolume (base*Parameters.m^(k+1)) (rows*Parameters.W^(k+1)) G S := by
  rw [parent_width,parent_prefix,packedVolume]

end
end CodedSorting.PhysicalRecursiveAdapters
end PhysicalRecursiveAdapters

section Packing
/-! Literal disk-address bridges at a recursive call boundary. Packing a
scalar into `m` short coordinates performs no disk transfer. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace CodedSorting.CommonRecursivePacking
open CommonSortingNormalization CommonPermutationPairs
open CommonLeafProgram (Disk)
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking
open CoordinateLayoutBridge ScalarLayoutBridge Address CodedSimulation PhysicalRecursiveExchange
noncomputable section

def packedShape (f P G S : ℕ) : EdgeAddress f P G S ≃
    FullAddress (Fin P) (Scalar (Parameters.m*f)) (Fin G) (Fin S) :=
  addressShape (Equiv.refl _) (blockPacking f) (Equiv.refl _) (Equiv.refl _)

theorem packed_address (f P G S : ℕ) (a : EdgeAddress f P G S) :
    (scalarLayout (Parameters.m*f) P G S (packedShape f P G S a)).val =
      (commonLayout f P G S a).val := by
  have h := congrArg Fin.val (blockPacking_same_address f P G S a)
  simpa only [finCongr_apply_coe,packedShape] using h

theorem packed_exchange (f P G S : ℕ) (a : EdgeAddress f P G S) :
    packedShape f P G S (exchangeEquiv.symm a) =
      exchangeEquiv.symm (packedShape f P G S a) := rfl

/-- A proved long-field exchange is the same actual scalar-field exchange,
with no repacking instruction and no new execution premise. -/
theorem scalar_of_long (q : Configuration) (f P G S source target : ℕ)
    (initial final : Disk q)
    (h : ∀ a : EdgeAddress f P G S,
      readBit q final target (commonLayout f P G S a).val =
      readBit q initial source (commonLayout f P G S (exchangeEquiv.symm a)).val)
    (a : FullAddress (Fin P) (Scalar (Parameters.m*f)) (Fin G) (Fin S)) :
    readBit q final target (scalarLayout (Parameters.m*f) P G S a).val =
      readBit q initial source
        (scalarLayout (Parameters.m*f) P G S (exchangeEquiv.symm a)).val := by
  let b := (packedShape f P G S).symm a
  have hab : packedShape f P G S b = a := Equiv.apply_symm_apply _ _
  have hb := packed_address f P G S b
  have he := packed_address f P G S (exchangeEquiv.symm b)
  rw [hab] at hb
  rw [packed_exchange,hab] at he
  rw [hb,he]
  exact h b

/-- The selected scalar child encodes its spectators in their existing
order; it keeps both scalar field values unchanged. -/
def childNumericShape (f P G S : ℕ) (c : Child) : ChildAddress f P G S c ≃
    FullAddress (Fin (childP f P c)) (Scalar f)
      (Fin (childG f G c)) (Fin (childS f S c)) :=
  addressShape (prefixCode f P c) (Equiv.refl _) (gapCode f G c) (suffixCode f S c)

theorem child_numeric_address (f P G S : ℕ) (c : Child)
    (a : ChildAddress f P G S c) :
    (scalarLayout f (childP f P c) (childG f G c) (childS f S c)
      (childNumericShape f P G S c a)).val =
      (ScalarLayoutBridge.childLayout f P G S c a).val := rfl

theorem child_no_repacking (f P G S : ℕ) (c : Child)
    (a : EdgeAddress f P G S) :
    (scalarLayout f (childP f P c) (childG f G c) (childS f S c)
      (childNumericShape f P G S c (childRepack f c a))).val =
      (commonLayout f P G S a).val := by
  rw [child_numeric_address]
  have h := congrArg Fin.val (child_common f P G S c a)
  simpa only [finCongr_apply_coe] using h

theorem child_numeric_exchange (f P G S : ℕ) (c : Child)
    (a : ChildAddress f P G S c) :
    childNumericShape f P G S c (exchangeEquiv.symm a) =
      exchangeEquiv.symm (childNumericShape f P G S c a) := rfl

/-- The child suffix remains word aligned after spectator regrouping. -/
theorem child_suffix_words (f S w : ℕ) (c : Child) :
    childS f (S*w) c = childS f S c*w := by
  rw [childS_eq,childS_eq]
  ring

theorem child_gap_positive (f G : ℕ) (c : Child) (hG : 0<G) :
    0<childG f G c := by
  rw [childG_eq]
  change 0 < (radix^f)^Fintype.card (SingleCoordinate.After (childRow c)) *
    (G * (radix^f)^Fintype.card (SingleCoordinate.Before (childCol c)))
  exact Nat.mul_pos (pow_pos (pow_pos radix_prime.pos _) _)
    (Nat.mul_pos hG (pow_pos (pow_pos radix_prime.pos _) _))

theorem child_suffix_aligned (f S w : ℕ) (c : Child) :
    w ∣ childS f (S*w) c := by
  rw [child_suffix_words]
  exact dvd_mul_left _ _

/-- Numeric field-width identity needed to lower the recursion depth. -/
theorem next_width (base k : ℕ) :
    base*Parameters.m^(k+1) = Parameters.m*(base*Parameters.m^k) := by
  rw [pow_succ]
  ring

/-- Numeric role-prefix identity needed by the next network layer. -/
theorem next_prefix (rows k : ℕ) :
    rows*Parameters.W^(k+1) = (rows*Parameters.W^k)*Parameters.W := by
  rw [pow_succ,Nat.mul_assoc]

end
end CodedSorting.CommonRecursivePacking
end Packing

section ExchangeChildren
/-! Smaller scalar programs become the literal selected-coordinate calls
inside an edge. The address identities below preserve every stored bit;
there is no uncharged conversion or assumed child execution. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonRecursiveExchange
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open PhysicalFieldPacking PhysicalRecursiveAdapters PhysicalRecursiveExchange
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge Circuit Address
noncomputable section

theorem child_scalar_address_val (f P G S : ℕ) (c : Child) (a : EdgeAddress f P G S) :
    (scalarLayout f (childP f P c) (childG f G c) (childS f S c)
      (childScalarShape f P G S c a)).val=(commonLayout f P G S a).val := by
  have h := congrArg Fin.val (child_scalar_address f P G S c a)
  simpa only [finCongr_apply_coe] using h

theorem scalarChildren_correct (q : Configuration) (f P G S : ℕ)
    (alloc : CommonRankEdge.Allocation q f P G S)
    (ps : ∀ c : Child,Program q f (childP f P c) (childG f G c) (childS f S c)
      alloc.source alloc.buffer alloc.limit)
    (c : Child) (s : Machine q) (F : EdgeStream f P G S)
    (hv : CommonRankEdge.View q f P G S alloc.source F s) :
    CommonRankEdge.View q f P G S alloc.source
      (transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) F)
      (executeRaw q (ps c).instructions s).1 := by
  intro a
  rw [←child_scalar_address_val f P G S c a,(ps c).correct]
  let b := (childScalarShape f P G S c).symm
    (exchange (childScalarShape f P G S c a))
  have hb : (scalarLayout f (childP f P c) (childG f G c) (childS f S c)
      (exchange (childScalarShape f P G S c a))).val=(commonLayout f P G S b).val := by
    simpa only [b,Equiv.apply_symm_apply] using child_scalar_address_val f P G S c b
  rw [hb,hv]
  exact congrFun (child_scalar_exchange f P G S c F) a

theorem scalarChildren_frame (q : Configuration) (f P G S : ℕ)
    (alloc : CommonRankEdge.Allocation q f P G S)
    (ps : ∀ c : Child,Program q f (childP f P c) (childG f G c) (childS f S c)
      alloc.source alloc.buffer alloc.limit)
    (c : Child) (s : Machine q) (i : Fin (q.N^q.exponent))
    (hi : i.val < alloc.source ∨ alloc.source+count q (longVolume f P G S) ≤ i.val)
    (hw : i.val < alloc.buffer ∨ alloc.limit ≤ i.val) :
    (executeRaw q (ps c).instructions s).1.disk i=s.disk i := by
  apply (ps c).frame s i _ hw
  simpa only [child_volume] using hi

/-- Concrete child instructions and their proved same-disk contracts. -/
def scalarChildren (q : Configuration) (f P G S : ℕ)
    (alloc : CommonRankEdge.Allocation q f P G S)
    (ps : ∀ c : Child,Program q f (childP f P c) (childG f G c) (childS f S c)
      alloc.source alloc.buffer alloc.limit) : CommonRankEdge.ChildProgram q f P G S alloc where
  instructions := fun c => (ps c).instructions
  correct := scalarChildren_correct q f P G S alloc ps
  frame := scalarChildren_frame q f P G S alloc ps
  safe := fun c => (ps c).safe

end
end CodedSorting.CommonRecursiveExchange
end ExchangeChildren

section ExchangeTree
/-! Public finite recursion trees for the actual common-machine exchange.
The tree contains dimensions and recursive calls, never payload data or
successful-execution certificates.  The workspace bound is deliberately
conservative: sibling calls reuse one interval whose size is bounded by
the sum of their individual requirements.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace CodedSorting.CommonRecursiveExchange
open CommonSortingNormalization CommonPermutationPairs
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking
noncomputable section

inductive Tree (q : Configuration) : ℕ → ℕ → ℕ → ℕ → Type
  | leaf (f P G S : ℕ) : Tree q f P G S
  | node (f R G S : ℕ) (gap_positive : 0<G) (suffix_positive : 0<S)
      (children : (c : Child) →
        Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c)) :
      Tree q (Parameters.m*f) (R*Parameters.W) G (S*q.w)

def space (q : Configuration) : {f P G S : ℕ} → Tree q f P G S → ℕ
  | f,P,G,S,.leaf _ _ _ _ => count q (ScalarVolume f P G S)
  | _,_,_,_,.node f R G S _ _ children =>
      count q (longVolume f (R*Parameters.W) G (S*q.w)) +
      CommonResidentNetwork.fileCount*count q (longVolume f R G (S*q.w)) +
      count q (longVolume f R G (S*q.w)) + ∑ c : Child,space q (children c)

theorem volume_le_space (q : Configuration) {f P G S : ℕ} (t : Tree q f P G S) :
    count q (ScalarVolume f P G S)≤space q t := by
  cases t with
  | leaf => exact le_rfl
  | node f R G S hG hS children =>
    rw [packedVolume]
    simp only [space]
    omega

theorem child_space_le (q : Configuration) (f R G S : ℕ)
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c)) (c : Child) :
    space q (children c)≤∑ d : Child,space q (children d) :=
  Finset.single_le_sum (f:=fun d : Child => space q (children d))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

end
end CodedSorting.CommonRecursiveExchange
end ExchangeTree

section ExchangeChildResources
/-! Resource adapters at abstract allocations. These theorem boundaries
prevent type conversion from expanding the concrete network constructor
when a scalar-program projection supplies a child cost certificate. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonRecursiveExchange
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking
noncomputable section
attribute [local irreducible] CommonResidentNetwork.edgeCount CircuitProgram.globalProgram Parameters.W

theorem scalarChildren_cost (q : Configuration) (f P G S : ℕ)
    (alloc : CommonRankEdge.Allocation q f P G S)
    (ps : ∀ c : Child,Program q f (childP f P c) (childG f G c) (childS f S c)
      alloc.source alloc.buffer alloc.limit) (c : Child) :
    cost q ((scalarChildren q f P G S alloc ps).instructions c)≤(ps c).charge :=
  (ps c).cost_le

theorem scalarChildren_length (q : Configuration) (f P G S : ℕ)
    (alloc : CommonRankEdge.Allocation q f P G S)
    (ps : ∀ c : Child,Program q f (childP f P c) (childG f G c) (childS f S c)
      alloc.source alloc.buffer alloc.limit) (c : Child) :
    ((scalarChildren q f P G S alloc ps).instructions c).length≤(ps c).charge :=
  (ps c).length_le

theorem scalarNetwork_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S)
    (p : CommonRecursiveNetwork.Layout q f P G S)
    (hbuffer : p.childBase+count q (longVolume f P G S)≤p.childLimit)
    (ps : ∀ c : Child,Program q f (childP f P c) (childG f G c) (childS f S c)
      (CommonRankEdge.networkAllocation q f P G S p hbuffer).source
      (CommonRankEdge.networkAllocation q f P G S p hbuffer).buffer
      (CommonRankEdge.networkAllocation q f P G S p hbuffer).limit) :
    cost q (CommonRecursiveNetwork.code q reader f P G S p
      (CommonRankEdge.networkEdgePrograms q reader f P G S hG hS p hbuffer
        (scalarChildren q f P G S (CommonRankEdge.networkAllocation q f P G S p hbuffer) ps)))≤
      CommonRecursiveExchangeCost.networkCharge q f P G S hG hS (fun c=>(ps c).charge) :=
  CommonRecursiveExchangeCost.network_cost q reader f P G S hG hS p hbuffer
    (scalarChildren q f P G S (CommonRankEdge.networkAllocation q f P G S p hbuffer) ps)
    (fun c=>(ps c).charge)
    (scalarChildren_cost q f P G S (CommonRankEdge.networkAllocation q f P G S p hbuffer) ps)

theorem scalarNetwork_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hG : 0<G) (hS : 0<S)
    (p : CommonRecursiveNetwork.Layout q f P G S)
    (hbuffer : p.childBase+count q (longVolume f P G S)≤p.childLimit)
    (ps : ∀ c : Child,Program q f (childP f P c) (childG f G c) (childS f S c)
      (CommonRankEdge.networkAllocation q f P G S p hbuffer).source
      (CommonRankEdge.networkAllocation q f P G S p hbuffer).buffer
      (CommonRankEdge.networkAllocation q f P G S p hbuffer).limit) :
    (CommonRecursiveNetwork.code q reader f P G S p
      (CommonRankEdge.networkEdgePrograms q reader f P G S hG hS p hbuffer
        (scalarChildren q f P G S (CommonRankEdge.networkAllocation q f P G S p hbuffer) ps))).length≤
      CommonRecursiveExchangeCost.networkCharge q f P G S hG hS (fun c=>(ps c).charge) :=
  CommonRecursiveExchangeCost.network_length q reader f P G S hG hS p hbuffer
    (scalarChildren q f P G S (CommonRankEdge.networkAllocation q f P G S p hbuffer) ps)
    (fun c=>(ps c).charge)
    (scalarChildren_length q f P G S (CommonRankEdge.networkAllocation q f P G S p hbuffer) ps)

end
end CodedSorting.CommonRecursiveExchange
end ExchangeChildResources

section ExchangeAllocation
/-! A concrete disjoint layout for one recursively executed parent. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace CodedSorting.CommonRecursiveExchange
open CommonSortingNormalization CommonPermutationPairs
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking
noncomputable section

def parentCount (q : Configuration) (f R G S : ℕ) :=
  count q (longVolume f (R*Parameters.W) G (S*q.w))
def childCount (q : Configuration) (f R G S : ℕ) :=
  count q (longVolume f R G (S*q.w))
def networkBase (q : Configuration) (f R G S buffer : ℕ) :=
  buffer+parentCount q f R G S
def childBase (q : Configuration) (f R G S buffer : ℕ) :=
  networkBase q f R G S buffer+CommonResidentNetwork.fileCount*childCount q f R G S

structure NodeAllocation (q : Configuration) (f R G S source buffer limit : ℕ) where
  source_separate : source+parentCount q f R G S≤buffer
  child_fits : childBase q f R G S buffer+childCount q f R G S≤limit
  fits : limit≤q.N^q.exponent

def outerSetup (q : Configuration) (f R G S source buffer limit : ℕ)
    (hS : 0<S) (a : NodeAllocation q f R G S source buffer limit) :
    CommonRecursiveOuter.Setup q where
  f:=f
  R:=R
  G:=G
  S:=S
  source:=source
  temporary:=buffer
  workspace:=networkBase q f R G S buffer
  suffix_positive:=hS
  fileStride:=childCount q f R G S
  live_le_stride:=by rw [childCount,CommonOneLevelAllocation.local_count]
  parents_separate:=a.source_separate
  network_separate:=le_rfl
  workspace_fits:=by
    have h:=a.child_fits
    have hf:=a.fits
    change childBase q f R G S buffer≤q.N^q.exponent
    omega

def networkLayout (q : Configuration) (f R G S source buffer limit : ℕ)
    (a : NodeAllocation q f R G S source buffer limit) :
    CommonRecursiveNetwork.Layout q f R G (S*q.w) where
  workspace:=networkBase q f R G S buffer
  stride:=childCount q f R G S
  childBase:=childBase q f R G S buffer
  childLimit:=limit
  count_le_stride:=le_rfl
  network_le_child:=le_rfl
  child_le_limit:=by have:=a.child_fits; omega
  fit:=a.fits

theorem scratch_separate (q : Configuration) (f R G S source buffer limit : ℕ)
    (a : NodeAllocation q f R G S source buffer limit) :
    CommonResidentNetwork.scratchBase (networkBase q f R G S buffer) (childCount q f R G S)+
      childCount q f R G S≤childBase q f R G S buffer := by
  exact CommonRankEdge.file_before_child q f R G (S*q.w)
    (networkLayout q f R G S source buffer limit a) (Sum.inr (Sum.inr ()))

def treeAllocation (q : Configuration) (f R G S source buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S)
    (children : (c : Child) → Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c))
    (hsep : source+count q (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w))≤buffer)
    (hwork : buffer+space q (.node f R G S hG hS children)≤limit)
    (hlimit : limit≤q.N^q.exponent) : NodeAllocation q f R G S source buffer limit where
  source_separate:=by simpa only [packedVolume,parentCount] using hsep
  child_fits:=by
    dsimp only [space] at hwork
    dsimp only [childBase,networkBase,parentCount,childCount]
    omega
  fits:=hlimit

theorem child_workspace (q : Configuration) (f R G S buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S)
    (children : (c : Child) → Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c))
    (hwork : buffer+space q (.node f R G S hG hS children)≤limit) (c : Child) :
    childBase q f R G S buffer+space q (children c)≤limit := by
  have hc:=child_space_le q f R G S children c
  dsimp only [space] at hwork
  dsimp only [childBase,networkBase,parentCount,childCount]
  omega

end
end CodedSorting.CommonRecursiveExchange
end ExchangeAllocation

section ExchangeFamily
/-! A generated recursion tree at every requested depth. All child shapes
come from the actual rank-selected coordinates of the network. No tree or
successful child execution is supplied by the caller. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace CodedSorting.CommonRecursiveExchange
open CommonSortingNormalization CommonPermutationPairs
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking
open CommonRecursivePacking RecursiveCallShape
noncomputable section

def canonical (q : Configuration) (base : ℕ) :
    (k rows G S : ℕ) → 0<G → 0<S →
      Tree q (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w)
  | 0,rows,G,S,_,_ => .leaf _ _ _ _
  | k+1,rows,G,S,hG,hS => by
      let f := base*Parameters.m^k
      let R := rows*Parameters.W^k
      have children : (c : Child) →
          Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c) := by
        intro c
        have t := canonical q base k (rows*beforeCard f (childRow c))
          (childG f G c) (childS f S c)
          (child_gap_positive f G c hG) (childS_pos f S c hS)
        simpa only [f,R,selected_prefix,child_suffix_words] using t
      have t := Tree.node f R G S hG hS children
      simpa only [f,R,next_width,next_prefix] using t

end
end CodedSorting.CommonRecursiveExchange
end ExchangeFamily
