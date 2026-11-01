import CodedSorting.Circuit.Local.SSAComposition

namespace CodedSorting.Construction.FiniteSSA.Verified
set_option autoImplicit false

theorem concat_toList_aux {α : Type} (chunks : List (Array α)) (start : Array α) :
    (chunks.foldl (fun a b => a ++ b) start).toList =
      start.toList ++ chunks.flatMap Array.toList := by
  induction chunks generalizing start with
  | nil => simp
  | cons c cs ih =>
      simpa only [List.foldl_cons, List.flatMap_cons, Array.toList_append,
        List.append_assoc] using ih (start ++ c)

/-- Open the concatenation only at the chunk level, never reduce large
concrete chunks while binding the certified trace to the original word. -/
theorem concat_toList {α : Type} (chunks : Array (Array α)) :
    (chunks.foldl (fun a b => a ++ b) #[]).toList =
      chunks.toList.flatMap Array.toList := by
  rw [← Array.foldl_toList, concat_toList_aux]
  simp

end CodedSorting.Construction.FiniteSSA.Verified

#print axioms CodedSorting.Construction.FiniteSSA.Verified.concat_toList
