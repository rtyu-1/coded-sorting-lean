import CodedSorting.Circuit.Local.ConcreteLocalProgram
import CodedSorting.Circuit.MemoryAccess.PhysicalFrameWordData
import CodedSorting.Circuit.Labels.FiniteProjectionEquations

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace CodedSorting.Construction.PhysicalFramePaths

open FiniteCertificate LocalPhysicalSemantics


private theorem empty_frames_bounded :
    (#[] : Array Nat).all (fun f => decide (f < 636)) = true := rfl

private theorem start_frames_chunk0_bounded :
    startFramesChunk0.all (fun f => decide (f < 636)) = true := by decide


private theorem start_frames_chunk1_bounded :
    startFramesChunk1.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk2_bounded :
    startFramesChunk2.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk3_bounded :
    startFramesChunk3.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk4_bounded :
    startFramesChunk4.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk5_bounded :
    startFramesChunk5.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk6_bounded :
    startFramesChunk6.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk7_bounded :
    startFramesChunk7.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk8_bounded :
    startFramesChunk8.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk9_bounded :
    startFramesChunk9.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk10_bounded :
    startFramesChunk10.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk11_bounded :
    startFramesChunk11.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk12_bounded :
    startFramesChunk12.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk13_bounded :
    startFramesChunk13.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk14_bounded :
    startFramesChunk14.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk15_bounded :
    startFramesChunk15.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk16_bounded :
    startFramesChunk16.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk17_bounded :
    startFramesChunk17.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk18_bounded :
    startFramesChunk18.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk19_bounded :
    startFramesChunk19.all (fun f => decide (f < 636)) = true := by decide

private theorem start_frames_chunk20_bounded :
    startFramesChunk20.all (fun f => decide (f < 636)) = true := by decide


private theorem final_frames_chunk0_bounded :
    finalFramesChunk0.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk1_bounded :
    finalFramesChunk1.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk2_bounded :
    finalFramesChunk2.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk3_bounded :
    finalFramesChunk3.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk4_bounded :
    finalFramesChunk4.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk5_bounded :
    finalFramesChunk5.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk6_bounded :
    finalFramesChunk6.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk7_bounded :
    finalFramesChunk7.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk8_bounded :
    finalFramesChunk8.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk9_bounded :
    finalFramesChunk9.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk10_bounded :
    finalFramesChunk10.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk11_bounded :
    finalFramesChunk11.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk12_bounded :
    finalFramesChunk12.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk13_bounded :
    finalFramesChunk13.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk14_bounded :
    finalFramesChunk14.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk15_bounded :
    finalFramesChunk15.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk16_bounded :
    finalFramesChunk16.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk17_bounded :
    finalFramesChunk17.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk18_bounded :
    finalFramesChunk18.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk19_bounded :
    finalFramesChunk19.all (fun f => decide (f < 636)) = true := by decide

private theorem final_frames_chunk20_bounded :
    finalFramesChunk20.all (fun f => decide (f < 636)) = true := by decide


attribute [local irreducible] startFrames finalFrames startFramesChunk0 startFramesChunk1 startFramesChunk2 startFramesChunk3 startFramesChunk4 startFramesChunk5 startFramesChunk6 startFramesChunk7 startFramesChunk8 startFramesChunk9 startFramesChunk10 startFramesChunk11 startFramesChunk12 startFramesChunk13 startFramesChunk14 startFramesChunk15 startFramesChunk16 startFramesChunk17 startFramesChunk18 startFramesChunk19 startFramesChunk20 finalFramesChunk0 finalFramesChunk1 finalFramesChunk2 finalFramesChunk3 finalFramesChunk4 finalFramesChunk5 finalFramesChunk6 finalFramesChunk7 finalFramesChunk8 finalFramesChunk9 finalFramesChunk10 finalFramesChunk11 finalFramesChunk12 finalFramesChunk13 finalFramesChunk14 finalFramesChunk15 finalFramesChunk16 finalFramesChunk17 finalFramesChunk18 finalFramesChunk19 finalFramesChunk20


theorem start_frames_bounded_check :
    startFrames.all (fun f => decide (f < 636)) = true := by
  rw [startFrames_append]
  simp only [Array.all_append, start_frames_chunk0_bounded, start_frames_chunk1_bounded, start_frames_chunk2_bounded, start_frames_chunk3_bounded, start_frames_chunk4_bounded, start_frames_chunk5_bounded, start_frames_chunk6_bounded, start_frames_chunk7_bounded, start_frames_chunk8_bounded, start_frames_chunk9_bounded, start_frames_chunk10_bounded, start_frames_chunk11_bounded, start_frames_chunk12_bounded, start_frames_chunk13_bounded, start_frames_chunk14_bounded, start_frames_chunk15_bounded, start_frames_chunk16_bounded, start_frames_chunk17_bounded, start_frames_chunk18_bounded, start_frames_chunk19_bounded, start_frames_chunk20_bounded, empty_frames_bounded, Bool.and_self]


theorem final_frames_bounded_check :
    finalFrames.all (fun f => decide (f < 636)) = true := by
  rw [finalFrames_append]
  simp only [Array.all_append, final_frames_chunk0_bounded, final_frames_chunk1_bounded, final_frames_chunk2_bounded, final_frames_chunk3_bounded, final_frames_chunk4_bounded, final_frames_chunk5_bounded, final_frames_chunk6_bounded, final_frames_chunk7_bounded, final_frames_chunk8_bounded, final_frames_chunk9_bounded, final_frames_chunk10_bounded, final_frames_chunk11_bounded, final_frames_chunk12_bounded, final_frames_chunk13_bounded, final_frames_chunk14_bounded, final_frames_chunk15_bounded, final_frames_chunk16_bounded, final_frames_chunk17_bounded, final_frames_chunk18_bounded, final_frames_chunk19_bounded, final_frames_chunk20_bounded, empty_frames_bounded, Bool.and_self]


theorem start_frames_size : startFrames.size = 661 := by
  rw [startFrames_append]
  simp only [Array.size_append, Array.size_empty]
  simp only [Nat.reduceAdd, startFramesChunk0_size, startFramesChunk1_size, startFramesChunk2_size, startFramesChunk3_size, startFramesChunk4_size, startFramesChunk5_size, startFramesChunk6_size, startFramesChunk7_size, startFramesChunk8_size, startFramesChunk9_size, startFramesChunk10_size, startFramesChunk11_size, startFramesChunk12_size, startFramesChunk13_size, startFramesChunk14_size, startFramesChunk15_size, startFramesChunk16_size, startFramesChunk17_size, startFramesChunk18_size, startFramesChunk19_size, startFramesChunk20_size]
theorem final_frames_size : finalFrames.size = 661 := by
  rw [finalFrames_append]
  simp only [Array.size_append, Array.size_empty]
  simp only [Nat.reduceAdd, finalFramesChunk0_size, finalFramesChunk1_size, finalFramesChunk2_size, finalFramesChunk3_size, finalFramesChunk4_size, finalFramesChunk5_size, finalFramesChunk6_size, finalFramesChunk7_size, finalFramesChunk8_size, finalFramesChunk9_size, finalFramesChunk10_size, finalFramesChunk11_size, finalFramesChunk12_size, finalFramesChunk13_size, finalFramesChunk14_size, finalFramesChunk15_size, finalFramesChunk16_size, finalFramesChunk17_size, finalFramesChunk18_size, finalFramesChunk19_size, finalFramesChunk20_size]


theorem start_frame_bounded (r : OriginalReg) : startFrames[r.val]! < 636 := by
  have hr : r.val < startFrames.size := by rw [start_frames_size]; exact r.isLt
  have h := of_decide_eq_true ((Array.all_eq_true (as := startFrames) (p := fun f => decide (f < 636))).mp start_frames_bounded_check r.val hr)
  simpa only [getElem!_pos startFrames r.val hr] using h


theorem final_frame_bounded (r : OriginalReg) : finalFrames[r.val]! < 636 := by
  have hr : r.val < finalFrames.size := by rw [final_frames_size]; exact r.isLt
  have h := of_decide_eq_true ((Array.all_eq_true (as := finalFrames) (p := fun f => decide (f < 636))).mp final_frames_bounded_check r.val hr)
  simpa only [getElem!_pos finalFrames r.val hr] using h


theorem forward_event_bounded (e : FrameEvent) (he : e ∈ forwardEvents) : e.frame < 636 := by
  simp only [forwardEvents, List.mem_append, List.mem_map] at he
  rcases he with ((h | h) | h) | h
  · obtain ⟨g,hg,rfl⟩ := h
    exact ConcreteLocalProgram.prefix_frames g hg
  · obtain ⟨t,ht,rfl⟩ := h
    have ht' := List.mem_range.mp ht
    change 510 + t < 636
    omega
  · obtain ⟨g,_,rfl⟩ := h
    change 0 < 636
    decide
  · obtain ⟨g,hg,rfl⟩ := h
    exact ConcreteLocalProgram.suffix_frames g hg

private theorem event_visit_bounded (events : List FrameEvent)
    (hall : ∀ e, e ∈ events → e.frame < 636)
    (r f : Nat) (hf : f ∈ eventVisits r events) : f < 636 := by
  unfold eventVisits at hf
  obtain ⟨e,he,hef⟩ := List.mem_filterMap.mp hf
  split at hef
  · have hval : e.frame = f := Option.some.inj hef
    rw [← hval]
    exact hall e he
  · contradiction

attribute [local irreducible] gates projections forwardEvents eventVisits

theorem forward_visit_bounded (r f : Nat) (hf : f ∈ eventVisits r forwardEvents) : f < 636 :=
  event_visit_bounded forwardEvents forward_event_bounded r f hf


/-- Every projection used by every actual original-wire history is one of
the 636 algebraically checked matrices. -/
theorem actual_path_projection_equations (r : OriginalReg)
    (f : Nat) (hf : f ∈ startFrames[r.val]! ::
      eventVisits r.val forwardEvents ++ [finalFrames[r.val]!]) :
    IntegerProjection.ProjectionEquations projections[f]! := by
  apply allProjectionEquations f
  rcases List.mem_cons.mp hf with h | h
  · subst f
    exact start_frame_bounded r
  · rcases List.mem_append.mp h with h | h
    · exact forward_visit_bounded r.val f h
    · have he : f = finalFrames[r.val]! := List.mem_singleton.mp h
      subst f
      exact final_frame_bounded r

#print axioms actual_path_projection_equations

end CodedSorting.Construction.PhysicalFramePaths
