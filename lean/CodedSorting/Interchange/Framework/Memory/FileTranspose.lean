import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Perm.Basic

/-! Reorder a rectangular on-disk directory from row/key to key/row order. -/
namespace CodedSorting.FileTranspose
variable {α β : Type*}

def select (K : ℕ) (fallback : α) (rows : List (List α)) : List α :=
  (List.finRange K).flatMap (fun k => rows.map (fun row => row[k.val]?.getD fallback))

theorem enumerate_row (K : ℕ) (fallback : α) (row : List α) (h : row.length = K) :
    (List.finRange K).map (fun k => row[k.val]?.getD fallback) = row := by
  subst K
  calc
    (List.finRange row.length).map (fun k => row[k.val]?.getD fallback) =
        (List.finRange row.length).map (fun k => row[k.val]) := by
      apply List.map_congr_left
      intro k _
      rw [List.getElem?_eq_getElem k.isLt]
      rfl
    _ = row := List.finRange_map_getElem row

theorem select_perm (K : ℕ) (fallback : α) (rows : List (List α))
    (h : ∀ row ∈ rows, row.length = K) : (select K fallback rows).Perm rows.flatten := by
  induction rows with
  | nil => simp [select]
  | cons row rest ih =>
    have hp := List.map_append_flatMap_perm (List.finRange K)
      (fun k => row[k.val]?.getD fallback)
      (fun k => rest.map (fun row => row[k.val]?.getD fallback))
    have he := enumerate_row K fallback row (h row (by simp))
    rw [he] at hp
    change (select K fallback (row :: rest)).Perm (row ++ rest.flatten)
    exact hp.symm.trans ((ih (fun row hr => h row (by simp [hr]))).append_left row)

theorem map_select (K : ℕ) (fallback : α) (rows : List (List α)) (f : α → β) :
    (select K fallback rows).map f =
      select K (f fallback) (rows.map (List.map f)) := by
  simp [select, List.map_flatMap, List.map_map, Function.comp_def, List.getElem?_map,
    Option.getD_map]

end CodedSorting.FileTranspose
