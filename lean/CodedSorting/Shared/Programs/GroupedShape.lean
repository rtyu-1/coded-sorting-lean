import CodedSorting.Sorting.Local.Columnsort.GroupedRecursiveColumnsort

/-! Exact integer parameter selection for Appendix D.2. No real-number
rounding approximation is used to bound the smaller exchanged fields. -/
namespace CodedSorting.GroupedShape
open LocalShape GroupedRecursiveColumnsort

def groupSize (H n : ℕ) : ℕ := H^2/(8*n)
def memoryGroups (H n : ℕ) : ℕ := H/groupSize H n

/-- The proof carries multiplicative inequalities, avoiding lossy division
in the lower and upper comparisons D=Θ(n/H). -/
theorem group_bounds (H n : ℕ) (hH : 0 < H) (hHn : H ≤ n)
    (hg2 : 2 ≤ groupSize H n) :
    let g := groupSize H n
    let D := memoryGroups H n
    0 < g ∧ 0 < D ∧ 8*g ≤ H ∧ D*g ≤ H ∧ H ≤ 2*D*g ∧
      4*n ≤ D*H ∧ D*H ≤ 16*n ∧ groups g n ≤ D^2 ∧ groups g n*g ≤ 2*n := by
  dsimp only
  let g := groupSize H n
  let D := memoryGroups H n
  have hg : 0 < g := by dsimp [g]; omega
  have hn : 0 < n := by omega
  have hden : 0 < 8*n := by omega
  have hfloor : g*(8*n) ≤ H^2 := Nat.div_mul_le_self _ _
  have hrem := Nat.mod_lt (H^2) hden
  have he := Nat.mod_add_div (H^2) (8*n)
  have hupper : H^2 < (g+1)*(8*n) := by
    change H^2%(8*n)+(8*n)*g = H^2 at he
    nlinarith only [hrem,he]
  have hgH : 8*g ≤ H := by
    have hmul := Nat.mul_le_mul_left (8*g) hHn
    nlinarith only [hfloor,hmul,hH]
  have hsmallg : g ≤ H := by omega
  have hD : 0 < D := by
    dsimp [D,memoryGroups]
    exact Nat.div_pos hsmallg hg
  have hDg : D*g ≤ H := Nat.div_mul_le_self H g
  have hremD := Nat.mod_lt H hg
  have heD := Nat.mod_add_div H g
  change H%g+g*D=H at heD
  have hhalf : H ≤ 2*D*g := by nlinarith only [heD,hremD,hD]
  have hHsq : H^2 ≤ 2*D*g*H := by
    have hm := Nat.mul_le_mul_right H hhalf
    nlinarith only [hm]
  have hlow : 4*n ≤ D*H := by nlinarith only [hfloor,hHsq,hg]
  have hupper' : H^2 < 16*n*g := by
    have h2 : g+1 ≤ 2*g := by omega
    have hm := Nat.mul_le_mul_right (8*n) h2
    nlinarith only [hupper,hm]
  have hhigh : D*H ≤ 16*n := by
    have hm := Nat.mul_le_mul_right H hDg
    nlinarith only [hm,hupper',hg]
  have hcapacity : 2*n ≤ D^2*g := by
    have hsquare := Nat.mul_self_le_mul_self hhalf
    nlinarith only [hsquare,hfloor,hg]
  have hgroups := groups_capacity g hg n
  have hgN : g ≤ n := le_trans hsmallg hHn
  have hz : groups g n ≤ D^2 := by nlinarith only [hgroups.2,hgN,hcapacity,hg]
  have hv : groups g n*g ≤ 2*n := by omega
  exact ⟨hg,hD,hgH,hDg,hhalf,hlow,hhigh,hz,hv⟩

/-- A precise upper bound on D using the integer excess-size ratio n/H. -/
theorem memoryGroups_le_ratio (H n : ℕ) (hH : 0 < H) (hHn : H ≤ n)
    (hg2 : 2 ≤ groupSize H n) : memoryGroups H n ≤ 32*(n/H) := by
  have h := group_bounds H n hH hHn hg2
  have hhigh : memoryGroups H n*H ≤ 16*n := h.2.2.2.2.2.2.1
  have hq : 0 < n/H := Nat.div_pos hHn hH
  have hrem := Nat.mod_lt n hH
  have he := Nat.mod_add_div n H
  have hn : n < 2*(n/H)*H := by nlinarith only [hrem,he,hq]
  nlinarith only [hhigh,hn,hH]

/-- Every exchanged field at any valid recursive node has width bounded by
3+floor(log₂(floor(n/H))); its size no longer depends on log H. -/
theorem field_width_bound (H n : ℕ) (hH : 0 < H) (hHn : H ≤ n)
    (hg2 : 2 ≤ groupSize H n) (m : ℕ) (hm : m ≤ memoryGroups H n^2) :
    sizeExponent m ≤ Nat.log 2 (n/H)+3 := by
  let L := Nat.log 2 (n/H)
  have hD := memoryGroups_le_ratio H n hH hHn hg2
  have hq : n/H < 2^(L+1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hDpow : memoryGroups H n ≤ 2^(L+6) := by
    have hm := Nat.mul_le_mul_left 32 (Nat.le_of_lt hq)
    have he : 32*2^(L+1) = 2^(L+6) := by
      rw [show L+6=(L+1)+5 by omega,pow_add]
      norm_num
      ring
    nlinarith only [hD,hm,he]
  have hnPow : m ≤ 2^(2*(L+6)) := by
    calc
      m ≤ memoryGroups H n^2 := hm
      _ ≤ (2^(L+6))^2 := Nat.pow_le_pow_left hDpow _
      _ = _ := by rw [←pow_mul]; ring_nf
  have ht := exponent_of_power_le m (2*(L+6)) hnPow
  change sizeExponent m ≤ L+3
  omega

end CodedSorting.GroupedShape
