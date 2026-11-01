import CodedSorting.Shared.Memory.EdgeReadBit

section ShapeStatefulRecursiveExchange
/-! Array shapes and control state for recursive file calls. The definitions describe the current call, its child request, and how a child result restores the parent computation. 

-/

set_option maxRecDepth 10000
set_option maxHeartbeats 600000
namespace CodedSorting.ShapeStatefulRecursiveExchange
open FullShapeControl FullShapeContinuation FullShapeAllocation RecursiveControl
open RecursiveExchange RecursiveExchangeCost
noncomputable section
variable {N exponent B w : ℕ}

/-- The lane shape is populated from the real recursive row count and the
actual finite spectator types, not from a caller-supplied surrogate volume. -/
def actualLaneShape (base k rows : ℕ) (Gap Suffix : Type)
    [Fintype Gap] [Fintype Suffix] : Shape :=
  laneShape base k rows (Fintype.card Gap) (Fintype.card Suffix)

theorem actualLaneShape_fields (base k rows : ℕ) (Gap Suffix : Type)
    [Fintype Gap] [Fintype Suffix] :
    let s := actualLaneShape base k rows Gap Suffix
    s.depth=k+1 ∧ s.width=base*Parameters.m^k ∧ s.rows=rows ∧
      s.prefixCount=rows*Parameters.W^k ∧ s.gap=Fintype.card Gap ∧
      s.suffix=Fintype.card Suffix ∧
      s.volume=longVolume (base*Parameters.m^k) (rows*Parameters.W^k)
        (Fintype.card Gap) (Fintype.card Suffix) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Numeric dimensions for the actual selected-coordinate child. File
placement is installed separately from the allocator before encoding. -/
def childShape (lane : Shape) (c : Child) : Shape :=
  { lane with
    depth := lane.depth-1
    rows := lane.rows*beforeCard lane.width (childRow c)
    prefixCount := childP lane.width lane.prefixCount c
    gap := childG lane.width lane.gap c
    suffix := childS lane.width lane.suffix c }

theorem childShape_actual_cards (lane : Shape) (c : Child) :
    (childShape lane c).prefixCount=Fintype.card (ChildPrefix lane.width lane.prefixCount c) ∧
      (childShape lane c).gap=Fintype.card (ChildGap lane.width lane.gap c) ∧
      (childShape lane c).suffix=Fintype.card (ChildSuffix lane.width lane.suffix c) :=
  ⟨rfl,rfl,rfl⟩

theorem childShape_volume (lane : Shape) (c : Child)
    (hvolume : lane.volume=longVolume lane.width lane.prefixCount lane.gap lane.suffix) :
    let s := childShape lane c
    (s.prefixCount*(radix^s.width*s.gap))*(radix^s.width*s.suffix)=s.volume := by
  exact (child_volume lane.width lane.prefixCount lane.gap lane.suffix c).trans hvolume.symm

/-- Total construction checks the exact global bound. The successful branch
uses a bounded tuple; it never silently truncates a dimension or pointer. -/
def encodeShape (shape : Shape) (c : Child) :
    Option (FullShapeControl.Frame (N := N) (exponent := exponent)) :=
  if h : ∀ i, shape.values i ≤ N^exponent then some (makeFrame shape h c) else none

theorem encodeShape_exact (shape : Shape) (c : Child)
    (h : ∀ i, shape.values i ≤ N^exponent) :
    encodeShape shape c = some (makeFrame shape h c) := by
  simp only [encodeShape,dif_pos h]

structure ActiveState (N exponent B w : ℕ) where
  frame : FullShapeControl.Frame (N := N) (exponent := exponent)
  machine : FullShapeControl.State B w

/-- This is the complete fused return path for one recursive pivot. The
child's active frame is discarded on return; the next active frame is the
one decoded by the physical pop. No old shape is used after that return. -/
def descend (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (childFrame : FullShapeControl.Frame (N := N) (exponent := exponent))
    (child : ActiveState N exponent B w → Option (ActiveState N exponent B w))
    (state : ActiveState N exponent B w) : Option (ActiveState N exponent B w) :=
  (invokeWithFrame hN hw hB state.frame
    (fun machine => (child ⟨childFrame,machine⟩).map ActiveState.machine) state.machine).map
      (fun out => ⟨out.1,out.2⟩)

/-- Later address calculations obtain their numeric context through this
accessor, which reads the restored active frame in the result of descend. -/
def activeShape (state : ActiveState N exponent B w) : Shape := shapeOf state.frame

theorem descend_restores (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (childFrame : FullShapeControl.Frame (N := N) (exponent := exponent))
    (child : ActiveState N exponent B w → Option (ActiveState N exponent B w))
    (state returned output : ActiveState N exponent B w)
    (frames : List (FullShapeControl.Frame (N := N) (exponent := exponent)))
    (hchild : child ⟨childFrame,
      { state.machine with control := enterRuntime hN hw state.frame state.machine.control }⟩ = some returned)
    (hvalid : runtimeValid hN hw (state.frame::frames) returned.machine.control)
    (hout : descend hN hw hB childFrame child state = some output) :
    output.frame=state.frame ∧ runtimeValid hN hw frames output.machine.control := by
  let callback := fun machine : FullShapeControl.State B w =>
    (child (⟨childFrame,machine⟩ : ActiveState N exponent B w)).map ActiveState.machine
  have hc : callback { state.machine with control := enterRuntime hN hw state.frame state.machine.control } =
      some returned.machine := by
    dsimp only [callback]
    rw [hchild]
    rfl
  change (invokeWithFrame hN hw hB state.frame callback state.machine).map _ = some output at hout
  cases hi : invokeWithFrame hN hw hB state.frame callback state.machine with
  | none => rw [hi] at hout; contradiction
  | some out =>
    rw [hi] at hout
    have he : (⟨out.1,out.2⟩ : ActiveState N exponent B w) = output := Option.some.inj hout
    cases he
    exact invokeWithFrame_restored hN hw hB state.frame callback state.machine returned.machine
      frames hc hvalid out hi

theorem descend_active_shape (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (childFrame : FullShapeControl.Frame (N := N) (exponent := exponent))
    (child : ActiveState N exponent B w → Option (ActiveState N exponent B w))
    (state returned output : ActiveState N exponent B w)
    (frames : List (FullShapeControl.Frame (N := N) (exponent := exponent)))
    (hchild : child ⟨childFrame,
      { state.machine with control := enterRuntime hN hw state.frame state.machine.control }⟩ = some returned)
    (hvalid : runtimeValid hN hw (state.frame::frames) returned.machine.control)
    (hout : descend hN hw hB childFrame child state = some output) :
    activeShape output=activeShape state :=
  congrArg shapeOf (descend_restores hN hw hB childFrame child state returned output frames hchild hvalid hout).1

end
end CodedSorting.ShapeStatefulRecursiveExchange
end ShapeStatefulRecursiveExchange

section RecursiveCallShape
/-!
# The numeric boundary from a scalar recursive call to a network lane

A recursive call exchanges two scalar fields.  At a non-leaf call, each
field is split into `m` coordinates and the prefix into `W` roles.  The
selected child is again a scalar call.  These two kinds of shape are
separated below: applying `childShape` twice without converting the second
scalar call to a lane would incorrectly reuse the old width and volume.

Only numeric shapes are treated here.  File handles are retained as
metadata, not asserted to implement split/gather or allocation.
-/
namespace CodedSorting.RecursiveCallShape
open FullShapeControl FullShapeAllocation ShapeStatefulRecursiveExchange
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking
noncomputable section

structure ScalarCall where
  shape : Shape

structure NetworkLane where
  shape : Shape

/-- Complete scalar-call dimensions at depth k. -/
def scalarCall (base k rows G S : ℕ) : ScalarCall :=
  let f := base*Parameters.m^k
  let P := rows*Parameters.W^k
  ⟨⟨k,f,ScalarVolume f P G S,rows,P,G,S,0,0,0,0,0,0⟩⟩

/-- This conversion is used only at positive depth with exact divisibility.
The theorems below establish that divisibility for recursive call shapes. -/
def toLane (call : ScalarCall) : NetworkLane :=
  ⟨{ call.shape with
    width := call.shape.width / Parameters.m
    prefixCount := call.shape.prefixCount / Parameters.W
    volume := call.shape.volume / Parameters.W }⟩

def selectedCall (lane : NetworkLane) (c : Child) : ScalarCall :=
  ⟨childShape lane.shape c⟩

theorem scalar_width_divisible (base k : ℕ) :
    Parameters.m ∣ base*Parameters.m^(k+1) := by
  rw [pow_succ,← Nat.mul_assoc]
  exact dvd_mul_left _ _

theorem scalar_prefix_divisible (rows k : ℕ) :
    Parameters.W ∣ rows*Parameters.W^(k+1) := by
  rw [pow_succ,← Nat.mul_assoc]
  exact dvd_mul_left _ _

theorem scalar_volume_split (base k rows G S : ℕ) :
    (scalarCall base (k+1) rows G S).shape.volume =
      (laneShape base k rows G S).volume*Parameters.W := by
  have hf : base*Parameters.m^(k+1)=Parameters.m*(base*Parameters.m^k) := by
    rw [pow_succ]
    ring
  change ScalarVolume (base*Parameters.m^(k+1)) (rows*Parameters.W^(k+1)) G S = _
  rw [hf,packedVolume]
  simp only [laneShape,longVolume,pow_succ]
  ring

/-- The numeric division computes precisely the lane used by
`StatefulRecursiveExchange.run` at its full-level invocation. -/
theorem toLane_scalarCall (base k rows G S : ℕ) :
    (toLane (scalarCall base (k+1) rows G S)).shape = laneShape base k rows G S := by
  have hm : 0 < Parameters.m := by norm_num [Parameters.m_value]
  have hW : 0 < Parameters.W := by norm_num [Parameters.W_value]
  have hf : base*Parameters.m^(k+1)/Parameters.m=base*Parameters.m^k := by
    rw [pow_succ,← Nat.mul_assoc,Nat.mul_div_cancel _ hm]
  have hp : rows*Parameters.W^(k+1)/Parameters.W=rows*Parameters.W^k := by
    rw [pow_succ,← Nat.mul_assoc,Nat.mul_div_cancel _ hW]
  have hv := scalar_volume_split base k rows G S
  have hd : (scalarCall base (k+1) rows G S).shape.volume/Parameters.W =
      (laneShape base k rows G S).volume := by
    rw [hv,Nat.mul_div_cancel _ hW]
  unfold toLane
  change { (scalarCall base (k+1) rows G S).shape with
    width := base*Parameters.m^(k+1)/Parameters.m
    prefixCount := rows*Parameters.W^(k+1)/Parameters.W
    volume := (scalarCall base (k+1) rows G S).shape.volume/Parameters.W } = _
  rw [hf,hp,hd]
  rfl

/-- The prefix cardinality obtained by selecting a coordinate has the exact
rows-times-W-power form expected by the next recursive call. -/
theorem selected_prefix (base k rows : ℕ) (c : Child) :
    childP (base*Parameters.m^k) (rows*Parameters.W^k) c =
      (rows*beforeCard (base*Parameters.m^k) (childRow c))*Parameters.W^k := by
  simpa only [childP,Fintype.card_fin] using
    Fintype.card_congr (childPrefixLayout base k rows c)

/-- One complete call → lane → selected-child conversion.  Both the
scalar field width and the role prefix are normalized before selection. -/
theorem selected_scalarCall (base k rows G S : ℕ) (c : Child) :
    selectedCall (toLane (scalarCall base (k+1) rows G S)) c =
      scalarCall base k (rows*beforeCard (base*Parameters.m^k) (childRow c))
        (childG (base*Parameters.m^k) G c) (childS (base*Parameters.m^k) S c) := by
  apply congrArg ScalarCall.mk
  change childShape (toLane (scalarCall base (k+1) rows G S)).shape c = _
  rw [toLane_scalarCall]
  have hp := selected_prefix base k rows c
  have hv := child_volume (base*Parameters.m^k) (rows*Parameters.W^k) G S c
  have hvol : (laneShape base k rows G S).volume =
      ScalarVolume (base*Parameters.m^k)
        ((rows*beforeCard (base*Parameters.m^k) (childRow c))*Parameters.W^k)
        (childG (base*Parameters.m^k) G c) (childS (base*Parameters.m^k) S c) := by
    change longVolume _ _ _ _ = _
    rw [← hv,hp]
  simp only [selectedCall,childShape,laneShape,scalarCall,Nat.add_sub_cancel,hp]
  exact congrArg (fun v =>
    (⟨k,base*Parameters.m^k,v,rows*beforeCard (base*Parameters.m^k) (childRow c),
      (rows*beforeCard (base*Parameters.m^k) (childRow c))*Parameters.W^k,
      childG (base*Parameters.m^k) G c,childS (base*Parameters.m^k) S c,
      0,0,0,0,0,0⟩ : Shape)) hvol

/-- The next call has 1/W of the parent's volume, as required by the
recurrence.  Regrouping within a lane itself preserves the lane's volume. -/
theorem selected_scalar_volume (base k rows G S : ℕ) (c : Child) :
    (selectedCall (toLane (scalarCall base (k+1) rows G S)) c).shape.volume =
      (scalarCall base (k+1) rows G S).shape.volume/Parameters.W := by
  rfl

/-- At the next non-leaf visit the lane width shrinks once more. This is
the missing conversion that cannot be replaced by another `childShape`. -/
theorem next_lane_width (base k rows G S : ℕ) (c : Child) :
    (toLane (selectedCall (toLane (scalarCall base (k+2) rows G S)) c)).shape.width =
      base*Parameters.m^k := by
  rw [show k+2=(k+1)+1 by omega,selected_scalarCall,toLane_scalarCall]
  rfl

theorem next_lane_prefix (base k rows G S : ℕ) (c : Child) :
    (toLane (selectedCall (toLane (scalarCall base (k+2) rows G S)) c)).shape.prefixCount =
      (rows*beforeCard (base*Parameters.m^(k+1)) (childRow c))*Parameters.W^k := by
  rw [show k+2=(k+1)+1 by omega,selected_scalarCall,toLane_scalarCall]
  rfl


/-- Every dynamic field in a nonempty scalar call is bounded by its total
volume. This derives counter safety from the data volume, not from an
independent assumption for each recursively generated field. -/
theorem scalarCall_bound {N exponent : ℕ} (base k rows G S : ℕ)
    (hb : 0 < base) (hr : 0 < rows) (hG : 0 < G) (hS : 0 < S)
    (hV : (scalarCall base k rows G S).shape.volume ≤ N^exponent) :
    ∀ i, (scalarCall base k rows G S).shape.values i ≤ N^exponent := by
  let f := base*Parameters.m^k
  let P := rows*Parameters.W^k
  let Q := radix^f
  have hm : 2 ≤ Parameters.m := by norm_num [Parameters.m_value]
  have hW : 0 < Parameters.W := by norm_num [Parameters.W_value]
  have hP : 0 < P := Nat.mul_pos hr (pow_pos hW _)
  have hQ : 0 < Q := pow_pos radix_prime.pos _
  obtain ⟨hpv,hqv,hgv,hsv⟩ :=
    WordControl.address_dimensions_le_volume P Q G S hP hQ hG hS
  have hv : P*(Q*(G*(Q*S))) ≤ N^exponent := by
    convert hV using 1 <;> dsimp [scalarCall,ScalarVolume,f,P,Q] <;> ring
  have hfv : f ≤ N^exponent :=
    ((Nat.lt_pow_self radix_prime.one_lt).le.trans hqv).trans hv
  have hkf : k ≤ f :=
    (Nat.lt_pow_self (show 1 < Parameters.m by omega)).le.trans
      (Nat.le_mul_of_pos_left _ hb)
  have hrows : rows ≤ P := Nat.le_mul_of_pos_right _ (pow_pos hW _)
  intro i
  fin_cases i
  · exact hkf.trans hfv
  · exact hfv
  · exact hV
  · exact hrows.trans (hpv.trans hv)
  · exact hpv.trans hv
  · exact hgv.trans hv
  · exact hsv.trans hv
  all_goals exact Nat.zero_le _

/-- In particular every canonical child descriptor fits the same global
bound as its parent, even though its spectator dimensions have changed. -/
theorem selected_call_bound {N exponent : ℕ} (base k rows G S : ℕ) (c : Child)
    (hb : 0 < base) (hr : 0 < rows) (hG : 0 < G) (hS : 0 < S)
    (hV : (scalarCall base (k+1) rows G S).shape.volume ≤ N^exponent) :
    ∀ i, (selectedCall (toLane (scalarCall base (k+1) rows G S)) c).shape.values i ≤ N^exponent := by
  have hbcard : 0 < beforeCard (base*Parameters.m^k) (childRow c) :=
    pow_pos (pow_pos radix_prime.pos _) _
  have hgchild : 0 < childG (base*Parameters.m^k) G c := by
    letI : Nonempty (Fin G) := ⟨⟨0,hG⟩⟩
    exact Fintype.card_pos
  have hschild : 0 < childS (base*Parameters.m^k) S c := childS_pos _ _ _ hS
  have hvol : (selectedCall (toLane (scalarCall base (k+1) rows G S)) c).shape.volume ≤ N^exponent := by
    rw [selected_scalar_volume]
    exact (Nat.div_le_self _ _).trans hV
  rw [selected_scalarCall] at hvol ⊢
  exact scalarCall_bound base k _ _ _ hb (Nat.mul_pos hr hbcard) hgchild hschild hvol

end
end CodedSorting.RecursiveCallShape
end RecursiveCallShape
