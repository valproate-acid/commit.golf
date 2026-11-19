import CommitGolfCandidate.TwoPermutationPinnedStoredLeaf
import CommitGolfCandidate.QuadPinnedMargin

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleComp.DeferredSampling
set_option maxRecDepth 8192
set_option exponentiation.threshold 2100

private theorem quad_pinned_trace_probability {α : Type} (st : Strat PermState α) (q calls : Nat)
    (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q+2^31) (bounded : st.QB calls) :
    st.prob PState.init (fun _ finish => ¬ s3PinCall.badSpec.Good finish.trace ∧ finish.count ≤ calls) ≤
      (q : ℝ)/2^123 := by
  have fits : calls < Fintype.card S3State := by
    rw [s3_card_state]
    omega
  have raw := s3PinCall.prob_bad_le_inv (2^1344) (2^896) (2^1344) (2^896) (2^1345+2^897)
    calls fits s3_trunc_fiber s3_chop_fiber s3_pin_fiber s3_second_inputs (by norm_num) (by norm_num)
    st calls bounded.toIQB
  refine raw.trans ?_
  rw [s3_card_state]
  simp only [Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
  exact quad_pinned_collision_margin q calls positive small (by omega)

theorem quad_pinned_leaf_probability {α : Type} (layout : PeerLeafLayout) (compression : Compression)
    (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120)
    (replayed : calls ≤ q+2^31) (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compression,p⟩ (recordRows program))}[
      PinnedLeafWitness result.2] ≤ (q : ENNReal)/2^123 := by
  classical
  let st := toStrat compression (recordRows program)
  have budget : st.QB calls := to_strat_QB compression bounded
  have records := pinned_recorded_table compression program PState.init Trace.WF.nil
  have post := Strat.post_and records (Strat.post_QB budget PState.init)
  have evidence : st.prob PState.init (fun result _ => PinnedLeafWitness result.2) ≤
      st.prob PState.init (fun _ finish => ¬ s3PinCall.badSpec.Good finish.trace ∧ finish.count ≤ calls) := by
    refine Strat.prob_le_prob_of_post post ?_
    intro result finish facts hit
    exact ⟨pinned_witness_bad layout finish.trace result.2 facts.1.2 hit,by simpa [PState.init] using facts.2.2⟩
  rw [perm_sampling_prob]
  refine (ENNReal.ofReal_le_ofReal
    (evidence.trans (quad_pinned_trace_probability st q calls positive small replayed budget))).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,ENNReal.ofReal_pow (by norm_num)]
  norm_num

end TwoPermutationPrototype.Sampling
