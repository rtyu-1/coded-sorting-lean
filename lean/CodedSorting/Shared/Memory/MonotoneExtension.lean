import CodedSorting.Interchange.Framework.Memory.Reflection
import Mathlib.Data.Finset.Sort

/-! Extend an increasing finite embedding to a permutation by filling the
unused output positions in increasing order. Both directions split into
two increasing colours, hence use the existing linear-scan machine. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonMonotoneExtension
noncomputable section
variable {V M : ℕ}

def unused (e : Fin V→Fin M) : Finset (Fin M) := (Finset.univ.image e)ᶜ

theorem unused_card (e : Fin V→Fin M) (he : StrictMono e) :
    (unused e).card=M-V := by
  simp only [unused,Finset.card_compl,Finset.card_image_of_injective _ he.injective,
    Fintype.card_fin,Finset.card_univ]

def tailEmbedding (e : Fin V→Fin M) (he : StrictMono e) : Fin (M-V) ↪o Fin M :=
  (unused e).orderEmbOfFin (unused_card e he)

theorem tail_not_image (e : Fin V→Fin M) (he : StrictMono e) (x : Fin (M-V)) :
    tailEmbedding e he x∉Finset.univ.image e := by
  have h := Finset.orderEmbOfFin_mem (unused e) (unused_card e he) x
  exact Finset.mem_compl.mp h

def extend (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (x : Fin M) : Fin M :=
  if hx : x.val<V then e ⟨x.val,hx⟩
  else tailEmbedding e he ⟨x.val-V,by have := x.isLt; omega⟩

theorem extend_prefix (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (x : Fin V) :
    extend h e he (x.castLE h)=e x := by
  simp only [extend,Fin.coe_castLE,x.isLt,↓reduceDIte]

theorem extend_injective (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) :
    Function.Injective (extend h e he) := by
  intro x y hxy
  by_cases hx : x.val<V <;> by_cases hy : y.val<V
  · simp only [extend,dif_pos hx,dif_pos hy] at hxy
    exact Fin.ext (congrArg (fun z : Fin V => z.val) (he.injective hxy))
  · simp only [extend,dif_pos hx,dif_neg hy] at hxy
    exact False.elim ((tail_not_image e he _) (Finset.mem_image.mpr
      ⟨⟨x.val,hx⟩,Finset.mem_univ _,hxy⟩))
  · simp only [extend,dif_neg hx,dif_pos hy] at hxy
    exact False.elim ((tail_not_image e he _) (Finset.mem_image.mpr
      ⟨⟨y.val,hy⟩,Finset.mem_univ _,hxy.symm⟩))
  · simp only [extend,dif_neg hx,dif_neg hy] at hxy
    have hv := congrArg Fin.val ((tailEmbedding e he).injective hxy)
    apply Fin.ext
    change x.val-V=y.val-V at hv
    omega

def permutation (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) : Equiv.Perm (Fin M) :=
  Equiv.ofBijective (extend h e he) (extend_injective h e he).bijective_of_finite

@[simp] theorem perm_prefix (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (x : Fin V) :
    permutation h e he (x.castLE h)=e x := extend_prefix h e he x

@[simp] theorem inverse_embed (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (x : Fin V) :
    (permutation h e he).symm (e x)=x.castLE h := by
  rw [←perm_prefix h e he x,Equiv.symm_apply_apply]

def colour (V : ℕ) (x : Fin M) : Fin 2 := if x.val<V then 0 else 1

theorem increasing (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e)
    (x y : Fin M) (hxy : x<y) (hk : colour V x=colour V y) :
    permutation h e he x<permutation h e he y := by
  change extend h e he x<extend h e he y
  by_cases hx : x.val<V <;> by_cases hy : y.val<V
  · simp only [extend,dif_pos hx,dif_pos hy]
    exact he hxy
  · simp [colour,hx,hy] at hk
  · simp [colour,hx,hy] at hk
  · simp only [extend,dif_neg hx,dif_neg hy]
    apply (tailEmbedding e he).strictMono
    change x.val-V<y.val-V
    change x.val<y.val at hxy
    omega

def inverseColour (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (x : Fin M) : Fin 2 :=
  colour V ((permutation h e he).symm x)

theorem inverse_increasing (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e)
    (x y : Fin M) (hxy : x<y) (hk : inverseColour h e he x=inverseColour h e he y) :
    (permutation h e he).symm x<(permutation h e he).symm y := by
  by_contra hn
  rcases lt_or_eq_of_le (le_of_not_gt hn) with hlt|heq
  · have hh := increasing h e he _ _ hlt hk.symm
    simp only [Equiv.apply_symm_apply] at hh
    exact (not_lt_of_gt hxy) hh
  · have hh := congrArg (permutation h e he) heq
    simp only [Equiv.apply_symm_apply] at hh
    exact (ne_of_lt hxy) hh.symm

end
end CodedSorting.CommonMonotoneExtension
