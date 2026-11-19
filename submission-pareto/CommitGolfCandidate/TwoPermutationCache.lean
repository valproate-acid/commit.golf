import CommitGolfCandidate.TwoPermutationUniform

/-! Bidirectional table oracle. A stored proof of extendibility allows sampling
from fresh representatives without exposing any particular full completion. -/
namespace TwoPermutationPrototype.Sampling
open OracleComp

noncomputable instance {α : Type} [Fintype α] [DecidableEq α] : Fintype (BiPermutation α) :=
  Fintype.ofEquiv (Equiv.Perm α) (BiPermutation.equiv α)

private noncomputable def sampleFrom {α : Type} [Finite α] (inhabited : Nonempty α) : SampleableType α := by
  letI : Nonempty α := inhabited
  letI : Fintype α := Fintype.ofFinite α
  exact SampleableType.ofFintype α

structure PermutationCache (α : Type) where
  entries : List (α × α)
  consistent : Nonempty (Completion entries)

noncomputable def PermutationCache.example {α : Type} (cache : PermutationCache α) : Completion cache.entries :=
  Classical.choice cache.consistent

def PermutationCache.empty (α : Type) : PermutationCache α where
  entries := []
  consistent := ⟨⟨⟨id, id, fun _ => rfl, fun _ => rfl⟩, by simp [Agrees]⟩⟩

noncomputable def PermutationCache.completionSampler {α : Type} [Fintype α] [DecidableEq α]
    (cache : PermutationCache α) : SampleableType (Completion cache.entries) :=
  sampleFrom cache.consistent

noncomputable def PermutationCache.sample {α : Type} [Fintype α] [DecidableEq α]
    (cache : PermutationCache α) : ProbComp (Completion cache.entries) :=
  @uniformSample _ cache.completionSampler

noncomputable def PermutationCache.extendForward {α : Type} [DecidableEq α]
    (cache : PermutationCache α) (input : α) (fresh : UnusedInput cache.entries input)
    (answer : RemainingOutputs cache.entries) : PermutationCache α := by
  let initial := cache.example
  let anchor := readForward cache.entries input fresh initial
  let transferred := (forward_fiber_move cache.entries input fresh anchor answer).invFun ⟨initial, rfl⟩
  exact ⟨(input, answer.val) :: cache.entries, ⟨(forward_cons_transport cache.entries input fresh answer).toFun transferred⟩⟩

noncomputable def PermutationCache.extendInverse {α : Type} [DecidableEq α]
    (cache : PermutationCache α) (input : α) (fresh : UnusedOutput cache.entries input)
    (answer : RemainingInputs cache.entries) : PermutationCache α := by
  let initial := cache.example
  let anchor := readInverse cache.entries input fresh initial
  let transferred := (inverse_fiber_move cache.entries input fresh anchor answer).invFun ⟨initial, rfl⟩
  exact ⟨(answer.val, input) :: cache.entries, ⟨(inverse_cons_transport cache.entries input fresh answer).toFun transferred⟩⟩

noncomputable def PermutationCache.forwardSampler {α : Type} [Fintype α] [DecidableEq α]
    (cache : PermutationCache α) (input : α) (fresh : UnusedInput cache.entries input) :
    SampleableType (RemainingOutputs cache.entries) := sampleFrom ⟨readForward cache.entries input fresh cache.example⟩

noncomputable def PermutationCache.inverseSampler {α : Type} [Fintype α] [DecidableEq α]
    (cache : PermutationCache α) (input : α) (fresh : UnusedOutput cache.entries input) :
    SampleableType (RemainingInputs cache.entries) := sampleFrom ⟨readInverse cache.entries input fresh cache.example⟩

noncomputable def PermutationCache.forward {α : Type} [Fintype α] [DecidableEq α]
    (cache : PermutationCache α) (input : α) : ProbComp (α × PermutationCache α) := by
  classical
  exact if fresh : UnusedInput cache.entries input then
    do let answer ← @uniformSample _ (cache.forwardSampler input fresh)
       pure (answer.val, cache.extendForward input fresh answer)
  else pure (cache.example.val.forward input, cache)

noncomputable def PermutationCache.inverse {α : Type} [Fintype α] [DecidableEq α]
    (cache : PermutationCache α) (input : α) : ProbComp (α × PermutationCache α) := by
  classical
  exact if fresh : UnusedOutput cache.entries input then
    do let answer ← @uniformSample _ (cache.inverseSampler input fresh)
       pure (answer.val, cache.extendInverse input fresh answer)
  else pure (cache.example.val.inverse input, cache)

private theorem cached_forward {α : Type} (table : List (α × α)) (input : α)
    (old : ¬ UnusedInput table input) (p q : Completion table) : p.val.forward input = q.val.forward input := by
  classical
  by_contra different
  apply old
  intro row present equal
  apply different
  have left := p.property row present
  have right := q.property row present
  rw [equal] at left right
  exact left.trans right.symm

private theorem cached_inverse {α : Type} (table : List (α × α)) (input : α)
    (old : ¬ UnusedOutput table input) (p q : Completion table) : p.val.inverse input = q.val.inverse input := by
  classical
  by_contra different
  apply old
  intro row present equal
  apply different
  have left := (congrArg p.val.inverse (p.property row present).symm).trans (p.val.leftInverse row.1)
  have right := (congrArg q.val.inverse (q.property row present).symm).trans (q.val.leftInverse row.1)
  rw [equal] at left right
  exact left.trans right.symm

theorem PermutationCache.forward_step_eq {α β : Type} [Fintype α] [DecidableEq α]
    (cache : PermutationCache α) (input : α) (next : α → BiPermutation α → ProbComp β) :
    (do let p ← cache.sample; next (p.val.forward input) p.val) =ᵈ
      (do let (answer, cache') ← cache.forward input; let p ← cache'.sample; next answer p.val) := by
  classical
  unfold PermutationCache.forward
  split
  · rename_i fresh
    simp only [bind_assoc, pure_bind]
    letI := cache.completionSampler
    letI := cache.forwardSampler input fresh
    letI posterior (answer : RemainingOutputs cache.entries) :
        SampleableType (Completion ((input, answer.val) :: cache.entries)) :=
      (cache.extendForward input fresh answer).completionSampler
    exact uniform_forward_step cache.entries input fresh (readForward cache.entries input fresh cache.example)
      (fun answer p => next answer.val p.val)
  · rename_i old
    simp only [pure_bind]
    apply EvalDistEq.bind_right
    intro p
    rw [cached_forward cache.entries input old p cache.example]

theorem PermutationCache.inverse_step_eq {α β : Type} [Fintype α] [DecidableEq α]
    (cache : PermutationCache α) (input : α) (next : α → BiPermutation α → ProbComp β) :
    (do let p ← cache.sample; next (p.val.inverse input) p.val) =ᵈ
      (do let (answer, cache') ← cache.inverse input; let p ← cache'.sample; next answer p.val) := by
  classical
  unfold PermutationCache.inverse
  split
  · rename_i fresh
    simp only [bind_assoc, pure_bind]
    letI := cache.completionSampler
    letI := cache.inverseSampler input fresh
    letI posterior (answer : RemainingInputs cache.entries) :
        SampleableType (Completion ((answer.val, input) :: cache.entries)) :=
      (cache.extendInverse input fresh answer).completionSampler
    exact uniform_inverse_step cache.entries input fresh (readInverse cache.entries input fresh cache.example)
      (fun answer p => next answer.val p.val)
  · rename_i old
    simp only [pure_bind]
    apply EvalDistEq.bind_right
    intro p
    rw [cached_inverse cache.entries input old p cache.example]

end TwoPermutationPrototype.Sampling
