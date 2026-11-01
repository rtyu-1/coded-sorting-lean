import CodedSorting.Circuit.Framework.AffineStreams
import CodedSorting.Shared.Memory.PhysicalStreamCursor
import Mathlib.Data.List.Dedup

/-! A public, computable schedule of distinct source/destination block
pairs. A monotone stream meets at most the sum of the two block counts,
proved by an injective increasing coordinate-sum certificate. The schedule
contains no payload and has no assumed operation-count bound. -/
set_option autoImplicit false
namespace CodedSorting.MonotoneBlockPairs
open PhysicalStreamCursor
variable {Q K : ℕ}

def pair (e : Equiv.Perm (Fin Q)) (B : ℕ) (x : Fin Q) : ℕ×ℕ :=
  (x.val/B,(e x).val/B)

def pairs (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K) (B : ℕ) (k : Fin K) : List (ℕ×ℕ) :=
  (((List.finRange Q).filter (fun x => key x=k)).map (pair e B)).dedup

@[simp] theorem mem_pairs (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (B : ℕ) (k : Fin K) (a : ℕ×ℕ) :
    a∈pairs e key B k ↔ ∃ x : Fin Q, key x=k ∧ pair e B x=a := by
  simp [pairs,List.mem_dedup]

theorem pairs_nodup (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K) (B : ℕ) (k : Fin K) :
    (pairs e key B k).Nodup := List.nodup_dedup _

theorem pairs_cover (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (B : ℕ) (x : Fin Q) : pair e B x∈pairs e key B (key x) :=
  (mem_pairs e key B (key x) (pair e B x)).2 ⟨x,rfl,rfl⟩

theorem pair_bounds (e : Equiv.Perm (Fin Q)) (B : ℕ) (hB : 0<B) (x : Fin Q) :
    (pair e B x).1<blockCount B Q ∧ (pair e B x).2<blockCount B Q := by
  constructor
  · exact (cursor_live_iff B Q (x.val/B) hB).2 ((Nat.div_mul_le_self _ _).trans_lt x.isLt)
  · exact (cursor_live_iff B Q ((e x).val/B) hB).2 ((Nat.div_mul_le_self _ _).trans_lt (e x).isLt)

theorem ordered_pair (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (hinc : ∀ x y, x<y → key x=key y → e x<e y)
    (B : ℕ) (x y : Fin Q) (hxy : x≤y) (hk : key x=key y) :
    (pair e B x).1≤(pair e B y).1 ∧ (pair e B x).2≤(pair e B y).2 := by
  have hd : e x≤e y := by
    rcases lt_or_eq_of_le hxy with h|h
    · exact (hinc x y h hk).le
    · exact le_of_eq (congrArg e h)
  exact ⟨Nat.div_le_div_right hxy,Nat.div_le_div_right hd⟩

/-- Distinct block pairs in the same monotone stream have distinct
coordinate sums. This is the finite counting argument, not a supplied bound. -/
theorem sum_injective (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (hinc : ∀ x y, x<y → key x=key y → e x<e y)
    (B : ℕ) (k : Fin K) (a b : ℕ×ℕ)
    (ha : a∈pairs e key B k) (hb : b∈pairs e key B k)
    (hs : a.1+a.2=b.1+b.2) : a=b := by
  obtain ⟨x,hx,rfl⟩ := (mem_pairs e key B k a).1 ha
  obtain ⟨y,hy,rfl⟩ := (mem_pairs e key B k b).1 hb
  rcases le_total x y with hxy|hyx
  · obtain ⟨h1,h2⟩ := ordered_pair e key hinc B x y hxy (hx.trans hy.symm)
    apply Prod.ext <;> omega
  · obtain ⟨h1,h2⟩ := ordered_pair e key hinc B y x hyx (hy.trans hx.symm)
    apply Prod.ext <;> omega

theorem pairs_length_le (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (hinc : ∀ x y, x<y → key x=key y → e x<e y)
    (B : ℕ) (hB : 0<B) (k : Fin K) :
    (pairs e key B k).length≤2*blockCount B Q := by
  have hcard := Finset.card_le_card_of_injOn (s:=(pairs e key B k).toFinset)
    (t:=Finset.range (2*blockCount B Q)) (fun a : ℕ×ℕ => a.1+a.2)
    (by
      intro a ha
      obtain ⟨x,hx,rfl⟩ := (mem_pairs e key B k a).1 (List.mem_toFinset.1 ha)
      obtain ⟨h1,h2⟩ := pair_bounds e B hB x
      exact Finset.mem_range.2 (by dsimp only; omega))
    (by
      intro a ha b hb hs
      exact sum_injective e key hinc B k a b (List.mem_toFinset.1 ha) (List.mem_toFinset.1 hb) hs)
  simpa only [List.toFinset_card_of_nodup (pairs_nodup e key B k),Finset.card_range] using hcard

/-- The public list of colored block-pair jobs, grouped by stream. -/
def schedule (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K) (B : ℕ) : List (Fin K×(ℕ×ℕ)) :=
  (List.finRange K).flatMap (fun k => (pairs e key B k).map (fun a => (k,a)))

@[simp] theorem mem_schedule (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (B : ℕ) (k : Fin K) (a : ℕ×ℕ) :
    (k,a)∈schedule e key B ↔ a∈pairs e key B k := by
  simp [schedule]

theorem schedule_covers (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (B : ℕ) (x : Fin Q) : (key x,pair e B x)∈schedule e key B :=
  (mem_schedule e key B (key x) (pair e B x)).2 (pairs_cover e key B x)

theorem schedule_nodup (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K) (B : ℕ) :
    (schedule e key B).Nodup := by
  apply List.nodup_flatMap.2
  constructor
  · intro k hk
    exact (pairs_nodup e key B k).map (fun a b h => (Prod.mk.inj h).2)
  · apply (List.nodup_finRange K).imp
    intro k l hne a ha hb
    obtain ⟨x,hx,hxa⟩ := List.mem_map.1 ha
    obtain ⟨y,hy,hya⟩ := List.mem_map.1 hb
    exact hne (congrArg Prod.fst (hxa.trans hya.symm))

theorem schedule_length_le (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (hinc : ∀ x y, x<y → key x=key y → e x<e y)
    (B : ℕ) (hB : 0<B) : (schedule e key B).length≤2*K*blockCount B Q := by
  have aux (ks : List (Fin K)) :
      (ks.flatMap (fun k => (pairs e key B k).map (fun a => (k,a)))).length≤
        ks.length*(2*blockCount B Q) := by
    induction ks with
    | nil => simp
    | cons k ks ih =>
      have h := pairs_length_le e key hinc B hB k
      simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_cons]
      nlinarith
  have h := aux (List.finRange K)
  simpa only [schedule,List.length_finRange,Nat.mul_left_comm,Nat.mul_assoc] using h

/-- Finite-address validity of every scheduled job. -/
theorem schedule_bounds (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (B : ℕ) (hB : 0<B) (job : Fin K×(ℕ×ℕ))
    (hj : job∈schedule e key B) :
    job.2.1<blockCount B Q ∧ job.2.2<blockCount B Q := by
  obtain ⟨x,hx,hpair⟩ := (mem_pairs e key B job.1 job.2).1
    ((mem_schedule e key B job.1 job.2).1 hj)
  rw [←hpair]
  exact pair_bounds e B hB x

/-- Combined public-plan endpoint: exact coverage, no duplicate job, and
a proved scan-size length bound. The hypotheses concern only the public
permutation and its coloring, never the data moved by the machine. -/
theorem complete_schedule (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K)
    (hinc : ∀ x y, x<y → key x=key y → e x<e y)
    (B : ℕ) (hB : 0<B) :
    (schedule e key B).Nodup ∧
    (∀ x : Fin Q, (key x,pair e B x)∈schedule e key B) ∧
    (∀ job∈schedule e key B,
      job.2.1<blockCount B Q ∧ job.2.2<blockCount B Q) ∧
    (schedule e key B).length≤2*K*blockCount B Q :=
  ⟨schedule_nodup e key B,schedule_covers e key B,
    fun job hj => schedule_bounds e key B hB job hj,schedule_length_le e key hinc B hB⟩
end CodedSorting.MonotoneBlockPairs
