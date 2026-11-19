import CommitGolfCandidate.NonceChainOracle
import CommitGolfCandidate.TwoPermutationPinnedHidingTransport
import CommitGolfCandidate.PublicQueryList

/-! Query the honest digest tape before handing the public view to the observer.
The compression function is fixed throughout the permutation comparison. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)
local instance chainDiscrete {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 8192

def querySaltedDigest (m : Message) (r : CompleteSaltTape) (i : Index) :
    OracleComp World (BitVec 256) := do
  let a ← World.query (.inr (.inr (.inl (RV64.packBuffer (pinnedFirstInput (messageWords m i))))))
  let b ← World.query (.inr (.inr (.inl (RV64.packBuffer (pinnedSecondInput i (saltWords (r i)) (RV64.replyWords a) (messageWords m i))))))
  return outputDigest b

theorem query_salted_bound (m : Message) (r : CompleteSaltTape) (i : Index) :
    PublicQueryBound (querySaltedDigest m r i) 2 := by
  unfold querySaltedDigest
  exact ⟨(by change 1 ≤ 2;omega),fun a => ⟨(by change 1 ≤ 2-1;omega),fun b => trivial⟩⟩

theorem query_salted_run (o : Oracle) (m : Message) (r : CompleteSaltTape) (i : Index) :
    fixedOracleRun o (querySaltedDigest m r i) =
      pure (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m r i) := by
  rw [querySaltedDigest,fixed_oracle_run_public,fixed_oracle_run_public,fixed_oracle_run_pure]
  rfl

def queryDigests (m : Message) (r : CompleteSaltTape) : OracleComp World DigestTape := do
  let ds ← queryList (querySaltedDigest m r) (List.finRange LENGTH)
  return fun i => ds[i.val]?.getD 0

attribute [local irreducible] List.finRange queryList querySaltedDigest

theorem query_digests_bound (m : Message) (r : CompleteSaltTape) :
    PublicQueryBound (queryDigests m r) (2*LENGTH) := by
  have h := public_query_bound_bind (query_list_bound _ 2 (query_salted_bound m r) (List.finRange LENGTH))
    (fun ds => show PublicQueryBound (pure (fun i : Index => ds[i.val]?.getD 0) : OracleComp World _) 0 from trivial)
  simpa only [queryDigests,List.length_finRange,Nat.add_zero,Nat.mul_comm] using h

theorem query_digests_run (o : Oracle) (m : Message) (r : CompleteSaltTape) :
    fixedOracleRun o (queryDigests m r) = pure (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m r) := by
  rw [queryDigests,fixed_oracle_run_bind,query_list_reference o _ _ _ (fun i _ => query_salted_run o m r i),
    pure_bind,fixed_oracle_run_pure]
  apply congrArg pure
  funext i
  rw [List.getElem?_eq_getElem (by simp [i.isLt])]
  simp

noncomputable def guardedView {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n) (t : Nat)
    (aux : S) (root : Commitment) (proof : Proof) : OracleComp World O :=
  @ite _ (∀ root proof, PublicQueryBound (a.observe aux root proof) t) (Classical.propDecidable _)
    (a.observe aux root proof) (pure (support_nonempty (a.observe aux root proof)).some)

theorem guarded_view_bound {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n) (t : Nat)
    (aux : S) (root : Commitment) (proof : Proof) : PublicQueryBound (guardedView a t aux root proof) t := by
  unfold guardedView
  split
  · rename_i h
    exact h _ _
  · trivial

theorem reached_view {S O : Type} {n t : Nat} (o : Oracle) (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (ch : Hiding.HidingChallenge S n)
    (reached : ch ∈ support (fixedOracleRun o a.choose)) (root : Commitment) (proof : Proof) :
    guardedView a t ch.aux root proof = a.observe ch.aux root proof := by
  have possible : ch ∈ support a.choose := by
    rw [fixed_run_eq_simulate] at reached
    exact (support_simulateQ_subset _ _) reached
  have instrumented : ch ∈ support (Prod.fst <$> Hiding.counted a.choose) := by
    rw [show Prod.fst <$> Hiding.counted a.choose = a.choose from fst_map_costDist a.choose ⟨Oracle.callCost⟩]
    exact possible
  rw [support_map] at instrumented
  obtain ⟨⟨other,calls⟩,hit,eq⟩ := instrumented
  change other = ch at eq
  subst other
  have guard (root : Commitment) (proof : Proof) := (hiding_observe_query_bound a h (ch,calls) hit root proof).mono (Nat.sub_le _ _)
  exact if_pos guard

noncomputable def chainPublicComp {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (t : Nat) (build : TranscriptBuilder) (c : Compression) (b : Bool) (r : CompleteSaltTape) : OracleComp World O := do
  let ch ← a.choose
  let ds ← queryDigests (if b then ch.message₁ else ch.message₀) r
  let view := build c ch.positions (fun i => r i.val) ds
  guardedView a t ch.aux view.1 view.2

attribute [local irreducible] queryDigests guardedView

theorem chain_comp_bound {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : TranscriptBuilder) (c : Compression) (b : Bool) (r : CompleteSaltTape) :
    PublicQueryBound (chainPublicComp a t build c b r) (t + 2*LENGTH + t) := by
  unfold chainPublicComp
  rw [Nat.add_assoc]
  apply public_query_bound_bind (hiding_choose_query_bound a h)
  intro ch
  apply public_query_bound_bind (query_digests_bound _ _)
  intro ds
  exact guarded_view_bound a t ch.aux _ _

theorem chain_comp_run {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : TranscriptBuilder) (o : Oracle) (b : Bool) (r : CompleteSaltTape) :
    fixedOracleRun o (chainPublicComp a t build o.compression b r) =
      (do let ch ← fixedOracleRun o a.choose
          observeTranscriptView a (pinnedHonestView build) o.compression ch b (BiPermutation.equiv Block o.permutation) r) := by
  rw [chainPublicComp,fixed_oracle_run_bind]
  apply bind_congr_of_forall_mem_support
  intro ch hit
  rw [fixed_oracle_run_bind,query_digests_run,pure_bind,reached_view o a h ch hit]
  simp only [observeTranscriptView,pinnedHonestView,fixedOracle,Equiv.symm_apply_apply]

end TwoPermutationPrototype.Sampling
