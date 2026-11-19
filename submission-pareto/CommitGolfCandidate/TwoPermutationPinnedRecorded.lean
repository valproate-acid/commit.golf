import CommitGolfCandidate.TwoPermutationPinnedReplay
import CommitGolfCandidate.S3LeafBinding

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleSpec
set_option maxRecDepth 8192

/-- Each permutation row reported by the machine can be read in either direction
in the real adaptive permutation table. -/
def PinnedRowsStored (rows : List PublicRow) (t : Trace PermState) : Prop :=
  ∀ x y, PublicRow.permutation x y ∈ rows → ∃ e ∈ t, e.inp=x ∧ e.out=y

private theorem prepend_rows {α : Type} (st : Strat PermState (α × List PublicRow))
    (head : List PublicRow) (before current : PState PermState) (suffix : before.trace <:+ current.trace)
    (headRows : PinnedRowsStored head current.trace)
    (tailRows : st.post current fun result finish =>
      current.trace <:+ finish.trace ∧ PinnedRowsStored result.2 finish.trace) :
    (st.bind fun result => Strat.done (result.1,head ++ result.2)).post current fun result finish =>
      before.trace <:+ finish.trace ∧ PinnedRowsStored result.2 finish.trace := by
  apply Strat.post_bind
  refine Strat.post_mono ?_ tailRows
  rintro result finish ⟨later,stored⟩
  refine ⟨suffix.trans later,?_⟩
  intro x y hit
  rcases List.mem_append.mp hit with early | tail
  · obtain ⟨e,he,hin,hout⟩ := headRows x y early
    exact ⟨e,later.subset he,hin,hout⟩
  · exact stored x y tail

theorem pinned_recorded_table {α : Type} (compress : Compression) (program : OracleComp World α)
    (s : PState PermState) (wf : s.trace.WF) :
    (toStrat compress (recordRows program)).post s fun result finish =>
      s.trace <:+ finish.trace ∧ PinnedRowsStored result.2 finish.trace := by
  induction program using OracleComp.inductionOn generalizing s with
  | pure a =>
    exact ⟨List.suffix_refl _,fun x y h => by contradiction⟩
  | query_bind query next ih =>
    rw [record_rows_query]
    rcases query with coin | input | input | output
    · rw [to_strat_coins]
      intro answer
      try dsimp only
      rw [to_strat_map]
      exact prepend_rows _ _ s s (List.suffix_refl _)
        (fun x y h => by simp [queryRows] at h) (ih answer s wf)
    · rw [to_strat_compress,to_strat_map]
      exact prepend_rows _ _ s s (List.suffix_refl _)
        (fun x y h => by simp [queryRows] at h) (ih _ s wf)
    · rw [to_strat_permute]
      refine Strat.post_fwd wf fun answer nextState nextWF grows present _ => ?_
      try dsimp only
      rw [to_strat_map]
      refine prepend_rows _ _ s nextState grows ?_ (ih answer nextState nextWF)
      intro x y h
      have eq : x=input ∧ y=answer := by simpa [queryRows] using h
      obtain ⟨rfl,rfl⟩ := eq
      exact present
    · rw [to_strat_inverse]
      intro answer allowed
      try dsimp only
      rw [to_strat_map]
      let after : PState PermState := ⟨s.trace.stepI answer output,s.count+1⟩
      refine prepend_rows _ _ s after (Trace.suffix_stepI _ _ _) ?_ (ih answer after (wf.stepI allowed))
      intro x y h
      have eq : x=answer ∧ y=output := by simpa [queryRows] using h
      obtain ⟨e,he,hin,hout⟩ := Trace.mem_stepI_of_mem_invAns allowed
      exact ⟨e,he,hin.trans eq.1.symm,hout.trans eq.2.symm⟩

end TwoPermutationPrototype.Sampling
