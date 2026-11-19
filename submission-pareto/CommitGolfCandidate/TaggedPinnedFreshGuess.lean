import CommitGolfCandidate.TaggedPinnedHighSupport

namespace TwoPermutationPrototype.Sampling
open OracleComp
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

def PinnedHighCache.NewTail {base : Cache} (start finish : PinnedHighCache base) (guess : BitVec 1344) : Prop :=
  ∃ row ∈ finish.added, row ∉ start.added ∧ row.upper = guess

private theorem pinned_high_step_new_tail_le {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (input : Block) (room : cache.zero.entries.length ≤ 2^121) (guess : BitVec 1344) :
    Pr{let result ← pinnedHighStep cache slot input}[cache.NewTail result.2 guess] ≤ (1 : ENNReal)/2^1343 := by
  classical
  by_cases unused : UnusedInput cache.zero.entries input
  · have present := pinned_current_tails_nonempty cache.zero room
    have knownRoom : (pinnedCachedTails cache.zero).length ≤ 2^121 := by
      simpa only [pinnedCachedTails, List.length_map] using room
    let sample := samplePinnedUnusedTails (pinnedCachedTails cache.zero) present
    simp only [pinnedHighStep, unused, present, dite_true, bind_pure_comp, prEvent_map]
    refine (prEvent_mono sample
      (p := fun tail => cache.NewTail (cache.extend ⟨input, tail.val, slot⟩ unused tail.property) guess)
      (q := fun tail => tail.val = guess) ?_).trans
      (pinned_sample_tail_guess_le (pinnedCachedTails cache.zero) knownRoom present guess)
    intro tail reached
    obtain ⟨row, inTable, outside, hi⟩ := reached
    change row ∈ (⟨input, tail.val, slot⟩ : PinnedHighRow) :: cache.added at inTable
    rcases List.mem_cons.mp inTable with rfl | old
    · exact hi
    · exact False.elim (outside old)
  · simp only [pinnedHighStep, unused, dite_false, prEvent_pure]
    have impossible : ¬ cache.NewTail cache guess := fun ⟨_, yes, no, _⟩ => no yes
    simp [impossible]

/-- The high transcript may select fresh addresses adaptively. Each guessed
new tail is still charged once at a uniform draw from the remaining tails. -/
theorem pinned_high_new_tail_le {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (answers : List (BitVec 1344)) (plans : List PinnedHighPlan)
    (room : cache.zero.entries.length + plans.length ≤ 2^121) (guess : BitVec 1344) :
    Pr{let result ← runPinnedHigh cache slot answers plans}[cache.NewTail result.2 guess] ≤
      (plans.length : ENNReal)/2^1343 := by
  classical
  induction plans generalizing cache slot answers with
  | nil =>
    have impossible : ¬ cache.NewTail cache guess := fun ⟨_, yes, no, _⟩ => no yes
    simp [runPinnedHigh, impossible]
  | cons plan rest ih =>
    let sample := pinnedHighStep cache slot (plan answers)
    let next (head : BitVec 1344 × PinnedHighCache base) :=
      runPinnedHigh head.2 (slot+1) (head.1 :: answers) rest
    let bad (head : BitVec 1344 × PinnedHighCache base) := cache.NewTail head.2 guess
    let detects (last : List (BitVec 1344) × PinnedHighCache base) := cache.NewTail last.2 guess
    have one : Pr{let head ← sample}[bad head] ≤ (1 : ENNReal)/2^1343 :=
      pinned_high_step_new_tail_le cache slot (plan answers) (by omega) guess
    have later (head : BitVec 1344 × PinnedHighCache base) (present : head ∈ support sample) (safe : ¬ bad head) :
        Pr{let result ← next head}[detects result] ≤ (rest.length : ENNReal)/2^1343 := by
      have grows := pinned_high_step_length cache slot (plan answers) head present
      have roomNext : head.2.zero.entries.length + rest.length ≤ 2^121 := by
        simp only [List.length_cons] at room
        omega
      refine (prEvent_mono (next head) (p := detects) (q := fun last => head.2.NewTail last.2 guess) ?_).trans
        (ih head.2 (slot+1) (head.1 :: answers) roomNext)
      rintro last ⟨row, included, wasNot, hit⟩
      exact ⟨row, included, fun found => safe ⟨row, found, wasNot, hit⟩, hit⟩
    change Pr{let result ← sample >>= next}[detects result] ≤ _
    refine (prEvent_bind_le_prEvent_add_of_support sample next bad detects later).trans ?_
    refine (add_le_add one le_rfl).trans_eq ?_
    rw [List.length_cons, Nat.cast_succ, ENNReal.add_div, add_comm]

end TwoPermutationPrototype.Sampling
