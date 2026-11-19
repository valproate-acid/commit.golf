import CommitGolfCandidate.TwoPermutationSampling
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! The probability bridge from a transport between fibers to a uniform answer
followed by a uniform completion of the updated table. -/
namespace TwoPermutationPrototype.Sampling
open OracleComp

def Transport.toEquiv {α β : Type} (transport : Transport α β) : α ≃ β where
  toFun := transport.toFun
  invFun := transport.invFun
  left_inv := transport.leftInverse
  right_inv := transport.rightInverse

def BiPermutation.equiv (α : Type) : Equiv.Perm α ≃ BiPermutation α where
  toFun p := ⟨p, p.symm, p.left_inv, p.right_inv⟩
  invFun p := ⟨p.forward, p.inverse, p.leftInverse, p.rightInverse⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem uniform_transport_bind {α β γ : Type} [SampleableType α] [SampleableType β]
    (transport : Transport α β) (next : α → ProbComp γ) :
    (($ᵗ α) >>= next) =ᵈ (($ᵗ β) >>= fun value => next (transport.invFun value)) := by
  have bijective : Function.Bijective transport.invFun :=
    ⟨Function.LeftInverse.injective transport.rightInverse, fun value => ⟨transport.toFun value, transport.leftInverse value⟩⟩
  have mapped := SampleableType.map_uniformSample_evalDistEq_of_bijective bijective
  have bound := mapped.bind_left next
  simpa only [bind_map_left, Function.comp_def] using bound.symm

private theorem align_fiber {α β γ : Type} {read : α → β} {answer : β} (value : Fiber read answer)
    (next : ∀ reply : β, Fiber read reply → ProbComp γ) :
    next (read value.val) ⟨value.val, rfl⟩ = next answer value := by
  obtain ⟨value, rfl⟩ := value
  rfl

theorem uniform_fiber_reveal {α β γ : Type} [SampleableType α] [SampleableType β]
    (read : α → β) (anchor : β) (move : ∀ value, Transport (Fiber read value) (Fiber read anchor))
    [∀ reply : β, SampleableType (Fiber read reply)]
    (next : ∀ reply : β, Fiber read reply → ProbComp γ) :
    (do let value ← $ᵗ α; next (read value) ⟨value, rfl⟩) =ᵈ
      (do let reply ← $ᵗ β; let value ← $ᵗ Fiber read reply; next reply value) := by
  let packedNext : α → ProbComp γ := fun value => next (read value) ⟨value, rfl⟩
  have split := uniform_transport_bind (split_fibers read anchor move) packedNext
  apply split.trans
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro reply
  have transport := (uniform_transport_bind (move reply) (next reply)).symm
  simpa only [packedNext, split_fibers, align_fiber] using transport

theorem uniform_forward_step {α γ : Type} [DecidableEq α] (table : List (α × α)) (input : α)
    (fresh : UnusedInput table input) (anchor : RemainingOutputs table)
    [SampleableType (Completion table)] [SampleableType (RemainingOutputs table)]
    [∀ answer : RemainingOutputs table, SampleableType (Completion ((input, answer.val) :: table))]
    (next : ∀ answer : RemainingOutputs table, Completion ((input, answer.val) :: table) → ProbComp γ) :
    (do let p ← $ᵗ Completion table
        let answer := readForward table input fresh p
        next answer ((forward_cons_transport table input fresh answer).toFun ⟨p, rfl⟩)) =ᵈ
      (do let answer ← $ᵗ RemainingOutputs table
          let p ← $ᵗ Completion ((input, answer.val) :: table)
          next answer p) := by
  letI fiberSampler (answer : RemainingOutputs table) :
      SampleableType (Fiber (readForward table input fresh) answer) :=
    SampleableType.ofEquiv (forward_cons_transport table input fresh answer).toEquiv.symm
  have reveal := uniform_fiber_reveal (readForward table input fresh) anchor
    (forward_fiber_move table input fresh anchor)
    (fun answer fiber => next answer ((forward_cons_transport table input fresh answer).toFun fiber))
  apply reveal.trans
  apply EvalDistEq.bind_right
  intro answer
  exact (uniform_transport_bind (forward_cons_transport table input fresh answer).symm (next answer)).symm

theorem uniform_inverse_step {α γ : Type} [DecidableEq α] (table : List (α × α)) (input : α)
    (fresh : UnusedOutput table input) (anchor : RemainingInputs table)
    [SampleableType (Completion table)] [SampleableType (RemainingInputs table)]
    [∀ answer : RemainingInputs table, SampleableType (Completion ((answer.val, input) :: table))]
    (next : ∀ answer : RemainingInputs table, Completion ((answer.val, input) :: table) → ProbComp γ) :
    (do let p ← $ᵗ Completion table
        let answer := readInverse table input fresh p
        next answer ((inverse_cons_transport table input fresh answer).toFun ⟨p, rfl⟩)) =ᵈ
      (do let answer ← $ᵗ RemainingInputs table
          let p ← $ᵗ Completion ((answer.val, input) :: table)
          next answer p) := by
  letI fiberSampler (answer : RemainingInputs table) :
      SampleableType (Fiber (readInverse table input fresh) answer) :=
    SampleableType.ofEquiv (inverse_cons_transport table input fresh answer).toEquiv.symm
  have reveal := uniform_fiber_reveal (readInverse table input fresh) anchor
    (inverse_fiber_move table input fresh anchor)
    (fun answer fiber => next answer ((inverse_cons_transport table input fresh answer).toFun fiber))
  apply reveal.trans
  apply EvalDistEq.bind_right
  intro answer
  exact (uniform_transport_bind (inverse_cons_transport table input fresh answer).symm (next answer)).symm

end TwoPermutationPrototype.Sampling
