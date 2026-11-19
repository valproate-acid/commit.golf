import CommitGolfCandidate.TwoPermutationAdaptive

/-! Programming a permutation row swaps its output with the requested output.
The query and the reference reply together determine whether the answer changes. -/
namespace TwoPermutationPrototype.Sampling

def BiPermutation.program {α : Type} [DecidableEq α] (p : BiPermutation α) (input output : α) :
    BiPermutation α :=
  p.swapOutputs (p.forward input) output

@[simp] theorem BiPermutation.program_read {α : Type} [DecidableEq α]
    (p : BiPermutation α) (input output : α) : (p.program input output).forward input = output := by
  simp [BiPermutation.program, BiPermutation.swapOutputs]

theorem BiPermutation.program_forward_unchanged {α : Type} [DecidableEq α]
    (p : BiPermutation α) {input output query : α}
    (otherInput : query ≠ input) (otherOutput : p.forward query ≠ output) :
    (p.program input output).forward query = p.forward query := by
  have otherPivot : p.forward query ≠ p.forward input :=
    fun equal => otherInput ((Function.LeftInverse.injective p.leftInverse) equal)
  exact swap_other otherPivot otherOutput

theorem BiPermutation.program_inverse_unchanged {α : Type} [DecidableEq α]
    (p : BiPermutation α) {input output query : α}
    (otherInput : p.inverse query ≠ input) (otherOutput : query ≠ output) :
    (p.program input output).inverse query = p.inverse query := by
  have otherPivot : query ≠ p.forward input := by
    intro equal
    apply otherInput
    rw [equal, p.leftInverse]
  change p.inverse (swap (p.forward input) output query) = p.inverse query
  rw [swap_other otherPivot otherOutput]

def BiPermutation.programRows {α : Type} [DecidableEq α] (p : BiPermutation α) (rows : List (α × α)) :
    BiPermutation α :=
  rows.foldl (fun current row => current.program row.1 row.2) p

theorem BiPermutation.program_rows_forward_unchanged {α : Type} [DecidableEq α]
    (p : BiPermutation α) (rows : List (α × α)) (query : α)
    (outside : ∀ row ∈ rows, query ≠ row.1 ∧ p.forward query ≠ row.2) :
    (p.programRows rows).forward query = p.forward query := by
  induction rows generalizing p with
  | nil => rfl
  | cons head tail ih =>
    have known := outside head (List.mem_cons_self)
    have unchanged := p.program_forward_unchanged known.1 known.2
    change ((p.program head.1 head.2).programRows tail).forward query = p.forward query
    rw [ih _ (fun row present => by simpa only [unchanged] using outside row (List.mem_cons_of_mem _ present)),
      unchanged]

theorem BiPermutation.program_rows_inverse_unchanged {α : Type} [DecidableEq α]
    (p : BiPermutation α) (rows : List (α × α)) (query : α)
    (outside : ∀ row ∈ rows, p.inverse query ≠ row.1 ∧ query ≠ row.2) :
    (p.programRows rows).inverse query = p.inverse query := by
  induction rows generalizing p with
  | nil => rfl
  | cons head tail ih =>
    have known := outside head (List.mem_cons_self)
    have unchanged := p.program_inverse_unchanged known.1 known.2
    change ((p.program head.1 head.2).programRows tail).inverse query = p.inverse query
    rw [ih _ (fun row present => by simpa only [unchanged] using outside row (List.mem_cons_of_mem _ present)),
      unchanged]

theorem BiPermutation.program_preserves {α : Type} [DecidableEq α]
    (p : BiPermutation α) (known : List (α × α)) (agrees : Agrees known p)
    {input output : α} (inputUnused : UnusedInput known input)
    (outputUnused : UnusedOutput known output) :
    Agrees ((input, output) :: known) (p.program input output) := by
  intro row present
  rcases List.mem_cons.mp present with same | previous
  · subst row
    exact p.program_read input output
  · have answer := agrees row previous
    exact (p.program_forward_unchanged (inputUnused row previous)
      (answer.symm ▸ outputUnused row previous)).trans answer


open OracleComp

private theorem split_programmed {α : Type} [DecidableEq α]
    (table : List (α × α)) (input : α) (fresh : UnusedInput table input)
    (output : RemainingOutputs table) (p : Completion table) :
    (((forward_split table input fresh output).toFun p).2).val.val =
      p.val.program input output.val := rfl

/-- Starting with a uniform consistent permutation and swapping a fixed fresh
row into place gives the uniform completion of the enlarged table. -/
theorem program_uniform_completion {α β : Type} [Fintype α] [DecidableEq α]
    (cache : PermutationCache α) (input : α) (fresh : UnusedInput cache.entries input)
    (output : RemainingOutputs cache.entries) (next : BiPermutation α → ProbComp β) :
    (do let p ← cache.sample; next (p.val.program input output.val)) =ᵈ
      (do let p ← (cache.extendForward input fresh output).sample; next p.val) := by
  let transport := forward_split cache.entries input fresh output
  let intoCache := forward_cons_transport cache.entries input fresh output
  let : SampleableType (Completion cache.entries) := cache.completionSampler
  let : SampleableType (RemainingOutputs cache.entries) := cache.forwardSampler input fresh
  let : SampleableType (Completion ((input, output.val) :: cache.entries)) :=
    (cache.extendForward input fresh output).completionSampler
  let : SampleableType (Fiber (readForward cache.entries input fresh) output) :=
    SampleableType.ofEquiv intoCache.toEquiv.symm
  apply (uniform_transport_bind transport (fun p => next (p.val.program input output.val))).trans
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  trans (do let _old ← $ᵗ RemainingOutputs cache.entries
            let fiber ← $ᵗ Fiber (readForward cache.entries input fresh) output
            next fiber.val.val)
  · apply EvalDistEq.bind_right
    intro old
    apply EvalDistEq.bind_right
    intro fiber
    have same := congrArg (fun pair => pair.2.val.val) (transport.rightInverse (old, fiber))
    change ((transport.toFun (transport.invFun (old, fiber))).2).val.val = fiber.val.val at same
    rw [split_programmed] at same
    rw [same]
  · trans (do let fiber ← $ᵗ Fiber (readForward cache.entries input fresh) output; next fiber.val.val)
    · let : MeasurableSpace β := ⊤
      exact EvalDistEq.of_evalDist_eq (evalDist_bind_const _ _)
    · exact uniform_transport_bind intoCache (fun fiber => next fiber.val.val)

end TwoPermutationPrototype.Sampling
