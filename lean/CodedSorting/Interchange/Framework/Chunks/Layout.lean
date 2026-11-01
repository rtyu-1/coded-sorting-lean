import CodedSorting.Interchange.Framework.Recursion.OuterCopyFrame
import CodedSorting.Interchange.Framework.Memory.PhysicalPaddingExchange

/-! Pure address bridges for the finite-machine chunk exchange.  All codecs
below name the same integer bit address; no physical rearrangement is added.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonChunkLayout
open Address CoordinateScans PhysicalFieldPacking RecursiveExchange
open PhysicalChunkLayout
noncomputable section

abbrev Volume := BaseExchangeProgram.Volume

/-- Output-to-input permutation of a numeric, row-major field exchange. -/
def swap (P Q G S : ℕ) : Equiv.Perm (Fin (Volume P Q G S)) :=
  (BaseExchangeProgram.permutation (P:=P) (Q:=Q) (G:=G) (S:=S)).symm

theorem swap_encoded (P Q G S : ℕ)
    (a : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)) :
    swap P Q G S (lowLayout a)=lowLayout (exchange a) := by
  apply (BaseExchangeProgram.permutation (P:=P) (Q:=Q) (G:=G) (S:=S)).injective
  rw [swap,Equiv.apply_symm_apply,BaseExchangeProgram.permutation_encoded]
  rfl

/-- Scalar digits and numeric digits induce exactly the same bit permutation. -/
theorem scalar_correct_numeric {Value : Type*} (f P G S : ℕ)
    (input output : ℕ → Value)
    (h : ∀ a : CommonRecursiveBase.ScalarAddress f P G S,
      output (scalarLayout f P G S a).val=
        input (scalarLayout f P G S (exchange a)).val) :
    ∀ i : Fin (ScalarVolume f P G S),
      output i.val=input (swap P (radix^f) G S i).val := by
  intro i
  obtain ⟨a,rfl⟩ := (scalarLayout f P G S).surjective i
  change output (scalarLayout f P G S a).val=
    input ((CommonRecursiveBase.permutation f P G S).symm
      (scalarLayout f P G S a)).val
  rw [CommonRecursiveBase.permutation_inverse_encoded]
  exact h a

/-- Changing equal dimensions changes no address, including the pullback. -/
theorem swap_cast (P Q G S P' Q' G' S' : ℕ)
    (hP : P=P') (hQ : Q=Q') (hG : G=G') (hS : S=S')
    (hV : Volume P Q G S=Volume P' Q' G' S')
    (i : Fin (Volume P Q G S)) :
    finCongr hV (swap P Q G S i)=
      swap P' Q' G' S' (finCongr hV i) := by
  subst P'; subst Q'; subst G'; subst S'
  rfl

theorem swap_conjugate (P Q G S P' Q' G' S' : ℕ)
    (hP : P=P') (hQ : Q=Q') (hG : G=G') (hS : S=S')
    (hV : Volume P Q G S=Volume P' Q' G' S') :
    (finCongr hV).symm.trans ((swap P Q G S).trans (finCongr hV))=
      swap P' Q' G' S' := by
  subst P'; subst Q'; subst G'; subst S'
  rfl

theorem numeric_correct_cast {Value : Type*} (P Q G S P' Q' G' S' : ℕ)
    (hP : P=P') (hQ : Q=Q') (hG : G=G') (hS : S=S')
    (input output : ℕ → Value)
    (h : ∀ i : Fin (Volume P Q G S),
      output i.val=input (swap P Q G S i).val) :
    ∀ i : Fin (Volume P' Q' G' S'),
      output i.val=input (swap P' Q' G' S' i).val := by
  subst P'; subst Q'; subst G'; subst S'
  exact h

theorem head_address_val (P Q R G S : ℕ) (a : ProductAddress P Q R G S) :
    (lowLayout (headShape P Q R G S a)).val=(productLayout P Q R G S a).val :=
  congrArg Fin.val (head_address P Q R G S a)

theorem tail_address_val (P Q R G S : ℕ) (a : ProductAddress P Q R G S) :
    (lowLayout (tailShape P Q R G S a)).val=(productLayout P Q R G S a).val :=
  congrArg Fin.val (tail_address P Q R G S a)

theorem head_exchange_address_val (P Q R G S : ℕ)
    (a : ProductAddress P Q R G S) :
    (lowLayout (exchange (headShape P Q R G S a))).val=
      (productLayout P Q R G S (headSwitch a)).val := by
  have he := congrArg (headShape P Q R G S) (head_conjugate P Q R G S a)
  rw [Equiv.apply_symm_apply] at he
  rw [he,head_address_val]

theorem tail_exchange_address_val (P Q R G S : ℕ)
    (a : ProductAddress P Q R G S) :
    (lowLayout (exchange (tailShape P Q R G S a))).val=
      (productLayout P Q R G S (tailSwitch a)).val := by
  have he := congrArg (tailShape P Q R G S) (tail_conjugate P Q R G S a)
  rw [Equiv.apply_symm_apply] at he
  rw [he,tail_address_val]

theorem product_swap_encoded (P Q R G S : ℕ)
    (a : ProductAddress P Q R G S) :
    swap P (Q*R) G S (productLayout P Q R G S a)=
      productLayout P Q R G S (exchange a) :=
  swap_encoded P (Q*R) G S (productShape P Q R G S a)

/-- The head and tail subcalls compose on the original integer addresses. -/
theorem head_tail_correct {Value : Type*} (P Q R G S : ℕ)
    (input middle output : ℕ → Value)
    (hh : ∀ i : Fin (Volume P Q (R*G) (R*S)),
      middle i.val=input (swap P Q (R*G) (R*S) i).val)
    (ht : ∀ i : Fin (Volume (P*Q) R (G*Q) S),
      output i.val=middle (swap (P*Q) R (G*Q) S i).val) :
    ∀ i : Fin (Volume P (Q*R) G S),
      output i.val=input (swap P (Q*R) G S i).val := by
  intro i
  obtain ⟨a,rfl⟩ := (productLayout P Q R G S).surjective i
  have htail := ht (lowLayout (tailShape P Q R G S a))
  rw [tail_address_val,swap_encoded,tail_exchange_address_val] at htail
  have hhead := hh (lowLayout (headShape P Q R G S (tailSwitch a)))
  rw [head_address_val,swap_encoded,head_exchange_address_val,switch_complete] at hhead
  rw [htail,hhead,product_swap_encoded]

theorem head_tail_correct_words {Value : Type*} (P Q R G S w : ℕ)
    (input middle output : ℕ → Value)
    (hh : ∀ i : Fin (Volume P Q (R*G) ((R*S)*w)),
      middle i.val=input (swap P Q (R*G) ((R*S)*w) i).val)
    (ht : ∀ i : Fin (Volume (P*Q) R (G*Q) (S*w)),
      output i.val=middle (swap (P*Q) R (G*Q) (S*w) i).val) :
    ∀ i : Fin (Volume P (Q*R) G (S*w)),
      output i.val=input (swap P (Q*R) G (S*w) i).val := by
  apply head_tail_correct P Q R G (S*w) input middle output ?_ ht
  exact numeric_correct_cast P Q (R*G) ((R*S)*w) P Q (R*G) (R*(S*w))
    rfl rfl rfl (Nat.mul_assoc R S w) input middle hh

/-- A field with one value has the identity exchange, including empty files. -/
theorem swap_one (P G S : ℕ) : swap P 1 G S=Equiv.refl _ := by
  ext i
  obtain ⟨a,rfl⟩ := (lowLayout (P:=P) (Q:=1) (G:=G) (S:=S)).surjective i
  rw [swap_encoded]
  congr 1
  cases a with
  | mk p h g l s =>
      have he : h=l := Subsingleton.elim _ _
      simp only [exchange,he,Equiv.refl_apply]

end
end CodedSorting.CommonChunkLayout
