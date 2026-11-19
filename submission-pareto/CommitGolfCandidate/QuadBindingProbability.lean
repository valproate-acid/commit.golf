import CommitGolfCandidate.QuadBindingDomain
import CommitGolfCandidate.QuadSingleMargin
import CommitGolfCandidate.QuadPinnedProbability
import CommitGolfCandidate.TwoPermutationPinnedPeerLayout

/-! The two penta binding terms: pinned leaves (q/2^123) and single-call D5
collisions among all recorded public queries, including inverse hits of D5
(q/2^122). Their sum is below q/2^120; no compression term remains. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleComp.DeferredSampling
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 2100

private theorem penta_trunc_fiber (d : BitVec 256) :
    (Finset.univ.filter fun b : Block => pentaSingleCall.trunc b = d).card ≤ 2^1344 := by
  convert s3_trunc_fiber d using 1
  congr 1

private theorem penta_trace_probability {α : Type} (st : Strat PermState α) (q calls : Nat)
    (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q+2^31) :
    st.prob PState.init (fun _ finish => ¬ pentaSingleCall.badSpec.Good finish.trace ∧ finish.count ≤ calls) ≤
      (q : ℝ)/2^122 := by
  have fits : calls < Fintype.card Block := by
    rw [Fintype.card_bitVec]
    change calls < 2^1600
    omega
  have raw := prob_not_good_le pentaSingleCall.badSpec (2^1344) (2^1280) calls fits
    (fun _ old => ⟨Finset.univ.filter (fun b => pentaSingleCall.trunc b = pentaSingleCall.trunc old.out),
      penta_trunc_fiber _, fun _ hit => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit.2⟩⟩)
    (fun _ => ⟨∅,Nat.zero_le _,fun _ hit => by simp [SingleCall.badSpec] at hit⟩)
    (fun _ _ => ⟨∅,Nat.zero_le _,fun _ hit => by simp [SingleCall.badSpec] at hit⟩)
    (fun _ => ⟨Finset.univ.image pentaEncode,
      Finset.card_image_le.trans (by simp only [Finset.card_univ,Fintype.card_bitVec]; exact le_rfl),
      fun _ hit => by
        obtain ⟨x,hx⟩ := hit.2
        exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,hx⟩⟩) st
  refine raw.trans ?_
  rw [Fintype.card_bitVec]
  simp only [PERMUTATION_WIDTH,Nat.cast_pow,Nat.cast_ofNat]
  exact penta_single_collision_margin q calls positive small (by omega)

theorem penta_witness_probability {α : Type} (compression : Compression)
    (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120)
    (replayed : calls ≤ q+2^31) (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compression,p⟩ (recordRows program))}[
      PentaWitness result.2] ≤ (q : ENNReal)/2^122 := by
  let st := toStrat compression (recordRows program)
  have budget : st.QB calls := to_strat_QB compression bounded
  have records := pinned_recorded_table compression program PState.init Trace.WF.nil
  have post := Strat.post_and records (Strat.post_QB budget PState.init)
  have evidence : st.prob PState.init (fun result _ => PentaWitness result.2) ≤
      st.prob PState.init (fun _ finish => ¬ pentaSingleCall.badSpec.Good finish.trace ∧ finish.count ≤ calls) := by
    refine Strat.prob_le_prob_of_post post ?_
    intro result finish facts hit
    exact ⟨penta_witness_bad finish.trace result.2 facts.1.2 hit,by simpa [PState.init] using facts.2.2⟩
  rw [perm_sampling_prob]
  refine (ENNReal.ofReal_le_ofReal
    (evidence.trans (penta_trace_probability st q calls positive small replayed))).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,ENNReal.ofReal_pow (by norm_num)]
  norm_num

def PentaReplayEvidence (rows : List PublicRow) : Prop :=
  PinnedLeafWitness rows ∨ PentaWitness rows

abbrev PentaReplayBound :=
  ∀ (program : OracleComp World Unit) (q calls : Nat),
    1 ≤ q → q ≤ 2^120 → calls ≤ q+2^31 → PublicQueryBound (recordRows program) calls →
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      PentaReplayEvidence result.2] ≤ (q : ENNReal)/2^120

theorem PentaReplayEvidence.mono {earlier later : List PublicRow}
    (contained : ∀ row ∈ earlier, row ∈ later) (hit : PentaReplayEvidence earlier) : PentaReplayEvidence later := by
  rcases hit with h | h
  · obtain ⟨p,i,n,m,v,w,ha,hb,hc,hd,eq,ne⟩ := h
    exact Or.inl ⟨p,i,n,m,v,w,contained _ ha,contained _ hb,
      contained _ hc,contained _ hd,eq,ne⟩
  · exact Or.inr (h.mono contained)

private theorem penta_event_budget (q : Nat) :
    (q : ENNReal)/2^123 + (q : ENNReal)/2^122 ≤ (q : ENNReal)/2^120 := by
  have a : (q : ENNReal)/2^123 ≤ (q : ENNReal)/2^121 :=
    ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by decide)) _
  have b : (q : ENNReal)/2^122 ≤ (q : ENNReal)/2^121 :=
    ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by decide)) _
  have sum : (q : ENNReal)/2^121 + (q : ENNReal)/2^121 = (q : ENNReal)/2^120 := by
    rw [← ENNReal.add_div, ← two_mul]
    have factor : (2 : ENNReal)^121 = 2^120*2 := by rw [show 121=120+1 by decide,pow_add]; simp
    rw [factor,mul_comm 2 (q : ENNReal)]
    exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)
  exact (add_le_add a b).trans_eq sum

theorem penta_replay_bound : PentaReplayBound := by
  intro program q calls positive small replayed bounded
  unfold PentaReplayEvidence
  refine (prEvent_or_le _ _ _).trans ((add_le_add ?_ ?_).trans (penta_event_budget q))
  · simp only [Oracle.sample,bind_assoc,pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      quad_pinned_leaf_probability ⟨pinnedPeerSalt,pinned_first_peer,pinned_second_peer⟩
        compress program q calls positive small replayed bounded
  · simp only [Oracle.sample,bind_assoc,pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      penta_witness_probability compress program q calls positive small replayed bounded

end TwoPermutationPrototype.Sampling
