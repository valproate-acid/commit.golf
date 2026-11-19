import CommitGolfCandidate.TwoPermutationHidingOpened
import CommitGolfCandidate.HidingQueries

/-! The adaptive first stage, opened row generation, and unopened leaf
hiding for a commitment and proof built from a digest tape and opened salts. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192

noncomputable local instance stagedFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

local instance stagedDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

abbrev OpenedSalts (positions : Positions) := {i : Index // i ∈ positions} → BitVec 128

abbrev TranscriptBuilder :=
  Compression → (positions : Positions) → OpenedSalts positions → DigestTape → Commitment × Proof

def messageWords (message : Message) (index : Index) : Words 32 :=
  fun word => (message index).extractLsb' (64 * word.val) 64

def publicOpenedSalts {positions : Positions} (salts : OpenedSalts positions) (i : Index) : BitVec 128 :=
  if present : i ∈ positions then salts ⟨i, present⟩ else 0

noncomputable def readOpenedDigests (positions : Positions) (tape : List Block) : OpenedDigests positions :=
  fun i => (readSecondDigests tape)[positions.toList.idxOf i.val]?.getD 0

noncomputable def twoPhaseReference {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) : ProbComp Output := do
  let (challenge, initial) ← lazyRun compress adversary.choose (PermutationCache.empty Block)
  let salts ← $ᵗ OpenedSalts challenge.positions
  let plans := leafPlans (messageWords challenge.message₀) (publicOpenedSalts salts) challenge.positions.toList
  let (raw, seeded) ← runPrepared initial [] plans
  let observer := fun tape =>
    let (root, proof) := build compress challenge.positions salts tape
    adversary.observe challenge.aux root proof
  let message := if which then challenge.message₁ else challenge.message₀
  conditionalGame seeded (messageWords message) (readOpenedDigests challenge.positions raw.reverse) compress observer false

private theorem distance_bind_support_le {ι α : Type} (common : ProbComp ι)
    (left right : ι → ProbComp α) (error : ℝ) (nonneg : 0 ≤ error)
    (each : ∀ value ∈ support common, measureTVDist (left value) (right value) ≤ error) :
    measureTVDist (common >>= left) (common >>= right) ≤ error := by
  apply ENNReal.toReal_le_of_le_ofReal nonneg
  refine (measureETVDist_bind_left_le_tsum common left right).trans ?_
  calc
    _ ≤ ∑' x, Pr{let y ← common}[y = x] * ENNReal.ofReal error := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases present : x ∈ support common
      · exact mul_le_mul_of_nonneg_left
          ((ENNReal.le_ofReal_iff_toReal_le (measureETVDist_ne_top _ _) nonneg).2 (each x present)) zero_le
      · have zero : Pr{let y ← common}[y = x] = 0 :=
          (prEvent_eq_zero_iff common (· = x)).2 (fun y mem equal => present (equal ▸ mem))
        rw [zero, zero_mul, zero_mul]
    _ = _ := by rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

private theorem two_stage_observe_bound {State Output : Type} {openingSize budget : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (bounded : Hiding.QueryBound adversary budget)
    (compress : Compression) (result : Hiding.HidingChallenge State openingSize × Cache)
    (reached : result ∈ support (lazyRun compress adversary.choose (PermutationCache.empty Block)))
    (root : Commitment) (proof : Proof) :
    QueryBounded (adversary.observe result.1.aux root proof) budget := by
  have projected : result.1 ∈ support
      ((simulateQ (lazyHandler compress) adversary.choose).run' (PermutationCache.empty Block)) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨result, reached, rfl⟩
  have possible := support_simulateQ_run'_subset (lazyHandler compress) adversary.choose _ projected
  have instrumented : result.1 ∈ support (Prod.fst <$> Hiding.counted adversary.choose) := by
    rw [show Prod.fst <$> Hiding.counted adversary.choose = adversary.choose from
      fst_map_costDist adversary.choose ⟨Oracle.callCost⟩]
    exact possible
  rw [support_map] at instrumented
  obtain ⟨⟨challenge, calls⟩, counted, equal⟩ := instrumented
  change challenge = result.1 at equal
  subst challenge
  exact (hiding_observe_query_bound adversary bounded (result.1, calls) counted root proof).mono
    (Nat.sub_le _ _)

/-- For every fixed compression function and all opening sizes, the abstract
Merkle transcript experiment meets the original two-stage hiding game budget. -/
theorem two_phase_reference_hiding {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (budget : Nat) (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist (twoPhaseReference adversary build compress false)
      (twoPhaseReference adversary build compress true) ≤ min 1 (((budget : ℝ) + 1) / 2 ^ 120) := by
  unfold twoPhaseReference
  apply distance_bind_support_le _ _ _ _ (by positivity)
  intro first inFirst
  apply distance_bind_support_le _ _ _ _ (by positivity)
  intro salts _
  apply distance_bind_support_le _ _ _ _ (by positivity)
  intro opened inOpened
  have before : first.2.entries.length ≤ budget := by
    have count := lazy_cache_length compress adversary.choose (PermutationCache.empty Block) budget
      (hiding_choose_query_bound adversary bounded) first inFirst
    simpa only [PermutationCache.empty, List.length_nil, Nat.zero_add] using count
  obtain ⟨rows, layout, count, tags⟩ := prepared_opened_rows first.1.positions (messageWords first.1.message₀)
    (publicOpenedSalts salts) first.2 opened inOpened
  simp only [Bool.false_eq_true, ite_false, ite_true]
  apply conditional_two_message_hiding _ _ _ _ _ _ first.2.entries rows budget layout before count tags
  intro tape
  exact two_stage_observe_bound adversary bounded compress first inFirst _ _

end TwoPermutationPrototype.Sampling
