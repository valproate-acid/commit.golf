import CommitGolfCandidate.TwoPermutationBindingEvents
import VCVio.OracleComp.EvalDist.Sum

/-! The origin of a row is set by its first exposure. A repeated query in either
direction retains the row's origin. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp

inductive Origin where
  | forward
  | inverse
  deriving DecidableEq

abbrev History := List (Origin × Row)

structure SafeHistory (history : History) : Prop where
  inverseOutsideFirst : ∀ row, (Origin.inverse, row) ∈ history → row.1 ∉ firstDomain
  noJoin : ∀ a b, (Origin.forward, a) ∈ history → (Origin.inverse, b) ∈ history →
    outputSuffix a.2 ≠ inputMiddle b.1
  digestInjective : ∀ a b, (Origin.forward, a) ∈ history → (Origin.forward, b) ∈ history →
    outputDigest a.2 = outputDigest b.2 → a = b
  suffixInjective : ∀ a b, (Origin.forward, a) ∈ history → (Origin.forward, b) ∈ history →
    outputSuffix a.2 = outputSuffix b.2 → a = b

theorem SafeHistory.empty : SafeHistory [] := by
  constructor <;> simp

private theorem row_mem {history : History} {row : Row} {origin : Origin}
    (present : (origin, row) ∈ history) : row ∈ history.map Prod.snd :=
  List.mem_map.mpr ⟨(origin, row), present, rfl⟩

private theorem extend_injective {width : Nat} (history : History) (row : Row) (read : Block → BitVec width)
    (injective : ∀ a b, (Origin.forward, a) ∈ history → (Origin.forward, b) ∈ history →
      read a.2 = read b.2 → a = b)
    (avoids : ∀ old ∈ history.map Prod.snd, read row.2 ≠ read old.2) :
    ∀ a b, (Origin.forward, a) ∈ (Origin.forward, row) :: history →
      (Origin.forward, b) ∈ (Origin.forward, row) :: history →
      read a.2 = read b.2 → a = b := by
  intro a b aPresent bPresent equal
  rcases List.mem_cons.mp aPresent with aHead | aTail
  · cases aHead
    rcases List.mem_cons.mp bPresent with bHead | bTail
    · cases bHead
      rfl
    · exact False.elim (avoids b (row_mem bTail) equal)
  · rcases List.mem_cons.mp bPresent with bHead | bTail
    · cases bHead
      exact False.elim (avoids a (row_mem aTail) equal.symm)
    · exact injective a b aTail bTail equal

theorem SafeHistory.push_forward {history : History} {row : Row} (safe : SafeHistory history)
    (ok : ¬ forwardProjection (history.map Prod.snd) row.2) :
    SafeHistory ((Origin.forward, row) :: history) := by
  have digestAvoid (old) (present : old ∈ history.map Prod.snd) :
      outputDigest row.2 ≠ outputDigest old.2 :=
    fun equal => ok (Or.inl ⟨old, present, equal⟩)
  have suffixAvoid (old) (present : old ∈ history.map Prod.snd) :
      outputSuffix row.2 ≠ outputSuffix old.2 :=
    fun equal => ok (Or.inr (Or.inl ⟨old, present, equal⟩))
  refine ⟨?_, ?_, extend_injective history row outputDigest safe.digestInjective digestAvoid,
    extend_injective history row outputSuffix safe.suffixInjective suffixAvoid⟩
  · intro a present
    have tail : (Origin.inverse, a) ∈ history := by simpa using present
    exact safe.inverseOutsideFirst a tail
  · intro a b aPresent bPresent equal
    have bTail : (Origin.inverse, b) ∈ history := by simpa using bPresent
    rcases List.mem_cons.mp aPresent with aHead | aTail
    · cases aHead
      exact ok (Or.inr (Or.inr ⟨b, row_mem bTail, equal⟩))
    · exact safe.noJoin a b aTail bTail equal

theorem SafeHistory.push_inverse {history : History} {row : Row} (safe : SafeHistory history)
    (outside : row.1 ∉ firstDomain) (ok : ¬ inverseJoin (history.map Prod.snd) row.1) :
    SafeHistory ((Origin.inverse, row) :: history) := by
  constructor
  · intro a present
    rcases List.mem_cons.mp present with head | tail
    · cases head
      exact outside
    · exact safe.inverseOutsideFirst a tail
  · intro a b aPresent bPresent equal
    have aTail : (Origin.forward, a) ∈ history := by simpa using aPresent
    rcases List.mem_cons.mp bPresent with head | tail
    · cases head
      exact ok ⟨a, row_mem aTail, equal.symm⟩
    · exact safe.noJoin a b aTail tail equal
  · intro a b aPresent bPresent
    exact safe.digestInjective a b (by simpa using aPresent) (by simpa using bPresent)
  · intro a b aPresent bPresent
    exact safe.suffixInjective a b (by simpa using aPresent) (by simpa using bPresent)

theorem SafeHistory.forward_first {history : History} {a : Row} (safe : SafeHistory history)
    (present : a ∈ history.map Prod.snd) (first : a.1 ∈ firstDomain) :
    (Origin.forward, a) ∈ history := by
  obtain ⟨⟨origin, row⟩, mem, same⟩ := List.mem_map.mp present
  change row = a at same
  subst row
  cases origin
  · exact mem
  · exact False.elim (safe.inverseOutsideFirst a mem first)

theorem SafeHistory.forward_second {history : History} {a b : Row} (safe : SafeHistory history)
    (aPresent : (Origin.forward, a) ∈ history) (bPresent : b ∈ history.map Prod.snd)
    (join : outputSuffix a.2 = inputMiddle b.1) :
    (Origin.forward, b) ∈ history := by
  obtain ⟨⟨origin, row⟩, mem, same⟩ := List.mem_map.mp bPresent
  change row = b at same
  subst row
  cases origin
  · exact mem
  · exact False.elim (safe.noJoin a b aPresent mem join)

theorem SafeHistory.two_round_collision_impossible {history : History} {a₀ a₁ b₀ b₁ : Row}
    (safe : SafeHistory history) (a₀Present : a₀ ∈ history.map Prod.snd)
    (a₁Present : a₁ ∈ history.map Prod.snd) (b₀Present : b₀ ∈ history.map Prod.snd)
    (b₁Present : b₁ ∈ history.map Prod.snd) (a₀First : a₀.1 ∈ firstDomain)
    (a₁First : a₁.1 ∈ firstDomain) (join₀ : outputSuffix a₀.2 = inputMiddle b₀.1)
    (join₁ : outputSuffix a₁.2 = inputMiddle b₁.1) (equal : outputDigest b₀.2 = outputDigest b₁.2) :
    a₀ = a₁ ∧ b₀ = b₁ := by
  have a₀Forward := safe.forward_first a₀Present a₀First
  have a₁Forward := safe.forward_first a₁Present a₁First
  have b₀Forward := safe.forward_second a₀Forward b₀Present join₀
  have b₁Forward := safe.forward_second a₁Forward b₁Present join₁
  have bEqual := safe.digestInjective b₀ b₁ b₀Forward b₁Forward equal
  constructor
  · apply safe.suffixInjective a₀ a₁ a₀Forward a₁Forward
    rw [join₀, join₁, bEqual]
  · exact bEqual

private theorem extend_safe_forward {cache : Cache} {history : History} (same : cache.entries = history.map Prod.snd)
    (safe : SafeHistory history) (input : Block) (result : Block × Cache)
    (reached : result ∈ support (cache.forward input)) (good : ¬ newForwardProjection cache result) :
    ∃ final, result.2.entries = final.map Prod.snd ∧ SafeHistory final := by
  unfold PermutationCache.forward at reached
  split at reached
  · obtain ⟨answer, _, equal⟩ := (mem_support_bind_iff _ _ _).mp reached
    simp only [support_pure, Set.mem_singleton_iff] at equal
    subst result
    refine ⟨(Origin.forward, input, answer.val) :: history, ?_, safe.push_forward ?_⟩
    · simp [PermutationCache.extendForward, same]
    · intro bad
      apply good
      exact ⟨by simp [PermutationCache.extendForward], by simpa only [same] using bad⟩
  · simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact ⟨history, same, safe⟩

private theorem extend_safe_inverse {cache : Cache} {history : History} (same : cache.entries = history.map Prod.snd)
    (safe : SafeHistory history) (output : Block) (result : Block × Cache)
    (reached : result ∈ support (cache.inverse output)) (good : ¬ newInverseProjection cache result) :
    ∃ final, result.2.entries = final.map Prod.snd ∧ SafeHistory final := by
  unfold PermutationCache.inverse at reached
  split at reached
  · obtain ⟨answer, _, equal⟩ := (mem_support_bind_iff _ _ _).mp reached
    simp only [support_pure, Set.mem_singleton_iff] at equal
    subst result
    have growth : cache.entries.length < cache.entries.length + 1 := Nat.lt_succ_self _
    refine ⟨(Origin.inverse, answer.val, output) :: history, ?_, safe.push_inverse ?_ ?_⟩
    · simp [PermutationCache.extendInverse, same]
    · exact fun bad => good (Or.inl ⟨growth, bad⟩)
    · exact fun bad => good (Or.inr ⟨growth, by simpa only [same] using bad⟩)
  · simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact ⟨history, same, safe⟩

private theorem prEvent_bind_pointwise {ι α β : Type} (sample : ProbComp ι)
    (left : ι → ProbComp α) (right : ι → ProbComp β) (p : α → Prop) (q : β → Prop)
    (each : ∀ x ∈ support sample, Pr{let y ← left x}[p y] ≤ Pr{let z ← right x}[q z]) :
    Pr{let y ← sample >>= left}[p y] ≤ Pr{let z ← sample >>= right}[q z] := by
  rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases present : x ∈ support sample
  · exact mul_le_mul_of_nonneg_left (each x present) zero_le
  · have zero := (prEvent_eq_zero_iff sample (· = x)).2 (fun y mem equal => present (equal ▸ mem))
    simp [zero]

private theorem lazy_run_query (compress : Compression) {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) (cache : Cache) :
    lazyRun compress ((liftM (World.query query) : OracleComp World _) >>= next) cache =
      (lazyHandler compress query).run cache >>= fun result => lazyRun compress (next result.1) result.2 := by
  simp [lazyRun, simulateQ_bind, StateT.run_bind]

open MeasureTheory in
/-- An event impossible in all safe terminal row histories can occur only when
the adaptive scanner flags a fresh row. The event may inspect the final value
and cache, including rows exposed by an in-program replay. -/
theorem unsafe_result_le_scan {α : Type} (compress : Compression) (program : OracleComp World α)
    (event : α × Cache → Prop)
    (exclude : ∀ value cache history, cache.entries = history.map Prod.snd → SafeHistory history →
      ¬ event (value, cache))
    (cache : Cache) (history : History) (same : cache.entries = history.map Prod.snd) (safe : SafeHistory history) :
    Pr{let result ← lazyRun compress program cache}[event result] ≤
      Pr{let flagged ← scanPermutation compress program cache}[flagged = true] := by
  classical
  induction program using OracleComp.inductionOn generalizing cache history with
  | pure value =>
    simp [lazyRun, scanPermutation, simulateQ_pure, StateT.run_pure, exclude value cache history same safe]
  | query_bind query next ih =>
    rw [lazy_run_query]
    rcases query with coins | (input | (input | input))
    · simp only [lazyHandler, StateT.run_monadLift, bind_assoc, pure_bind]
      change Pr{let result ← ((_ : ProbComp _) >>= fun answer => lazyRun compress (next answer) cache)}[event result] ≤
        Pr{let flagged ← ((_ : ProbComp _) >>= fun answer => scanPermutation compress (next answer) cache)}[flagged = true]
      exact prEvent_bind_pointwise _ _ _ _ _ fun answer _ => ih answer cache history same safe
    · simp only [lazyHandler, StateT.run_pure, pure_bind]
      change _ ≤ Pr{let flagged ← scanPermutation compress (next (compress input)) cache}[flagged = true]
      exact ih (compress input) cache history same safe
    · change Pr{let result ← (cache.forward input >>= fun result => lazyRun compress (next result.1) result.2)}[event result] ≤
        Pr{let flagged ← (cache.forward input >>= fun result => if newForwardProjection cache result
          then pure true else scanPermutation compress (next result.1) result.2)}[flagged = true]
      apply prEvent_bind_pointwise
      intro result reached
      split
      · simp
      · rename_i good
        obtain ⟨newHistory, sameNew, safeNew⟩ := extend_safe_forward same safe input result reached good
        exact ih result.1 result.2 newHistory sameNew safeNew
    · change Pr{let result ← (cache.inverse input >>= fun result => lazyRun compress (next result.1) result.2)}[event result] ≤
        Pr{let flagged ← (cache.inverse input >>= fun result => if newInverseProjection cache result
          then pure true else scanPermutation compress (next result.1) result.2)}[flagged = true]
      apply prEvent_bind_pointwise
      intro result reached
      split
      · simp
      · rename_i good
        obtain ⟨newHistory, sameNew, safeNew⟩ := extend_safe_inverse same safe input result reached good
        exact ih result.1 result.2 newHistory sameNew safeNew


open MeasureTheory in
theorem unsafe_result_with_replay {α : Type} (compress : Compression) (program : OracleComp World α)
    (event : α × Cache → Prop)
    (exclude : ∀ value cache history, cache.entries = history.map Prod.snd → SafeHistory history →
      ¬ event (value, cache))
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : QueryBounded program calls) :
    Pr{let result ← lazyRun compress program (PermutationCache.empty Block)}[event result] ≤
      (q : ENNReal) / 2 ^ 122 := by
  exact (unsafe_result_le_scan compress program event exclude (PermutationCache.empty Block) [] rfl
      SafeHistory.empty).trans (scan_permutation_with_replay compress program q calls positive small withReplay bounded)

end TwoPermutationPrototype.Sampling
