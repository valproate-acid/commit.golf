import CommitGolfCandidate.PentaNonceView
import CommitGolfCandidate.PentaNonceFinal
import CommitGolfCandidate.PentaHidingTransport

/-! Hiding for the 5-ary tree + NonceChain (penta analogue of `QuadNonceSecurity`, itself the quad analogue of 31727a8's `NonceChainSecurity`).
Chain salts vs independent salts costs `chainError (2t + 2·LENGTH + LENGTH/4 + LENGTH/16 + LENGTH/64)` per side
(`nonce_chain_oracle_distance`); the independent-salt penta view costs `(t+1)/2^121`
(`penta_final_reference_hiding_sharp`); `penta_chain_budget` fits the sum under `(t+1)/2^120`. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces blocks)
local instance pentaChainSecurityDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem penta_chain_budget (t : Nat) :
    let q := t + 2*LENGTH + pentaQueries PENTA_LEVELS + t
    ((t : ℝ)+1)/2^121 +
      2 * (((blocks+1 : Nat) : ℝ) * ((2*q+(blocks+1) : ℝ)/2^192)) ≤
        ((t : ℝ)+1)/2^120 := by
  simp only [penta_queries_value]
  norm_num [blocks,LENGTH,LOG_LENGTH,Nat.cast_add,Nat.cast_mul]
  nlinarith [Nat.cast_nonneg (α := ℝ) t]

noncomputable def sampledPentaChain {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : PentaTranscriptBuilder) (b : Bool) : ProbComp O := do
  let o ← Oracle.sample
  let ch ← fixedOracleRun o a.choose
  let k ← $ᵗ Key
  observeTranscriptView a (pentaView build) o.compression ch b (BiPermutation.equiv Block o.permutation)
    (actualNonces o.permutation k)

theorem penta_chain_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : PentaTranscriptBuilder) (isLocal : PentaBuildLocal build) (b : Bool) :
    𝒟[sampledPentaChain a build b] =
      𝒟[($ᵗ Compression) >>= fun c => chainNonceGame c (chainPentaComp a t build b)] := by
  simp only [sampledPentaChain,Oracle.sample,bind_assoc,pure_bind,chainNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  apply _root_.evalDist_bind_congr; intro π
  simp_rw [chain_penta_comp_run a h build isLocal (⟨c,π⟩ : Oracle)]
  exact (distribution_bind_comm ($ᵗ Key) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm

theorem penta_iid_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : PentaTranscriptBuilder) (isLocal : PentaBuildLocal build) (b : Bool) :
    𝒟[sampledReferenceView a (pentaView build) b] =
      𝒟[($ᵗ Compression) >>= fun c => iidNonceGame c (chainPentaComp a t build b)] := by
  simp only [sampledReferenceView,Oracle.sample,bind_assoc,pure_bind,iidNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  trans 𝒟[do let π ← $ᵗ Perm
             let r ← $ᵗ SaltArray
             fixedOracleRun ⟨c,π⟩ (chainPentaComp a t build b r)]
  · apply _root_.evalDist_bind_congr; intro π
    simp_rw [chain_penta_comp_run a h build isLocal (⟨c,π⟩ : Oracle)]
    exact (distribution_bind_comm ($ᵗ SaltArray) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm
  · exact distribution_bind_comm _ _ _

theorem penta_chain_reference_hiding {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : PentaTranscriptBuilder) (isLocal : PentaBuildLocal build) :
    measureTVDist (sampledPentaChain a build false) (sampledPentaChain a build true) ≤
      min 1 (((t : ℝ)+1)/2^120) := by
  have side (b : Bool) :
      measureTVDist (sampledPentaChain a build b) (sampledReferenceView a (pentaView build) b) ≤
        chainError (t+2*LENGTH+pentaQueries PENTA_LEVELS+t) := by
    have d := measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression)
      (fun c => chainNonceGame c (chainPentaComp a t build b))
      (fun c => iidNonceGame c (chainPentaComp a t build b))
      (δ := chainError (t+2*LENGTH+pentaQueries PENTA_LEVELS+t)) (by unfold chainError;positivity)
      (fun c => nonce_chain_oracle_distance _ _ _ (chain_penta_comp_bound a h build b))
    simpa only [measureTVDist,penta_chain_grouped a h build isLocal b,penta_iid_grouped a h build isLocal b] using d
  refine le_min (measureTVDist_le_one _ _) ?_
  by_cases small : t+1 ≤ 2^120
  swap
  · apply (measureTVDist_le_one _ _).trans
    have large : 2^120 ≤ t+1 := by omega
    have castLarge : (2:ℝ)^120 ≤ (t:ℝ)+1 := by exact_mod_cast large
    exact (le_div_iff₀ (by positivity : 0<(2:ℝ)^120)).2 (by simpa using castLarge)
  have old : measureTVDist (sampledReferenceView a (pentaView build) false)
      (sampledReferenceView a (pentaView build) true) ≤ ((t:ℝ)+1)/2^121 := by
    unfold measureTVDist
    rw [(penta_sampled_reference_eq a build false).evalDist_eq,(penta_sampled_reference_eq a build true).evalDist_eq]
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    intro c
    exact penta_final_reference_hiding_sharp a build c t h small
  have right := side true
  rw [measureTVDist_comm] at right
  have combined := (measureTVDist_triangle (sampledPentaChain a build false)
    (sampledReferenceView a (pentaView build) false) _).trans
    (add_le_add (side false) ((measureTVDist_triangle _ (sampledReferenceView a (pentaView build) true) _).trans
      (add_le_add old right)))
  refine combined.trans ?_
  have bound := penta_chain_budget t
  unfold chainError
  linarith

private theorem executable_to_penta_chain {State Output : Type} {openingSize : Nat}
    (scheme : Scheme) (build : PentaTranscriptBuilder) (refines : PentaNonceTranscriptRefines scheme build)
    (adversary : Hiding.HidingAdversary State Output openingSize) (which : Bool) :
    Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =ᵈ
      sampledPentaChain adversary build which := by
  have grouping :
      Hiding.hidingExperiment scheme adversary which = (do
        let challenge ← adversary.choose
        let message := if which then challenge.message₁ else challenge.message₀
        let (root, proof) ← executableTranscript scheme message challenge.positions
        adversary.observe challenge.aux root proof) := by
    simp [Hiding.hidingExperiment, executableTranscript, bind_assoc]
  have counted :
      Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =
        (Oracle.sample >>= fun oracle => fixedOracleRun oracle (Hiding.hidingExperiment scheme adversary which)) := by
    simp only [Hiding.runHiding, fixedOracleRun, map_eq_bind_pure_comp, Function.comp_def]
  rw [counted]
  unfold sampledPentaChain
  apply EvalDistEq.bind_right Oracle.sample
  intro oracle
  rw [grouping, fixed_oracle_run_bind]
  apply EvalDistEq.bind_right
  intro challenge
  rw [fixed_oracle_run_bind]
  let message := if which then challenge.message₁ else challenge.message₀
  apply ((refines oracle message challenge.positions).bind_left
    (fun (view : Commitment × Proof) => fixedOracleRun oracle
      (adversary.observe challenge.aux view.1 view.2))).trans
  simp only [bind_assoc, pure_bind, observeTranscriptView, message]
  apply EvalDistEq.bind_right
  intro salts
  have equivalentOracle : fixedOracle oracle.compression (BiPermutation.equiv Block oracle.permutation) = oracle := by
    unfold fixedOracle
    rw [Equiv.symm_apply_apply]
  rw [equivalentOracle]
  rfl

/-- Hiding of any scheme whose executable transcript is the penta honest view with nonce-chain
salts, for a builder that reads the node function only on honest inputs. -/
theorem penta_nonce_hiding_of_transcript (scheme : Scheme) (build : PentaTranscriptBuilder)
    (isLocal : PentaBuildLocal build) (refines : PentaNonceTranscriptRefines scheme build) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  constructor
  · intro _ budget
    positivity
  · intro openingSize budget _ State Output adversary bounded
    unfold measureTVDist
    rw [(executable_to_penta_chain scheme build refines adversary false).evalDist_eq,
      (executable_to_penta_chain scheme build refines adversary true).evalDist_eq]
    exact penta_chain_reference_hiding adversary bounded build isLocal

/-- The form the lead wires into `Solution.lean` (privacy line). -/
theorem penta_nonce_hiding (scheme : Scheme) (refines : PentaNonceTranscriptRefines scheme pentaTranscriptBuilder) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) :=
  penta_nonce_hiding_of_transcript scheme pentaTranscriptBuilder penta_transcript_builder_local refines

end TwoPermutationPrototype.Sampling
