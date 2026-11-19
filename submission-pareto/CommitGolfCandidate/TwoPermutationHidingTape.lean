import CommitGolfCandidate.TwoPermutationHidingHits

/-! The reference tape can be drawn as three independent parts, even when the
opening set was chosen by a previous adaptive computation. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

abbrev PrivateLeafKey := BitVec 128 × Block × BitVec 1344
abbrev DigestTape := Index → BitVec 256
abbrev OpenTape (positions : Positions) := {i : Index // i ∈ positions} → PrivateLeafKey
abbrev HiddenTape (positions : Positions) := {i : Index // i ∉ positions} → PrivateLeafKey
abbrev FullTape := Index → BitVec 256 × PrivateLeafKey

noncomputable local instance finiteFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

noncomputable def sampleHiddenTape (positions : Positions) : ProbComp (HiddenTape positions) :=
  $ᵗ HiddenTape positions

def functionPairEquiv (ι α β : Type) : (ι → α × β) ≃ ((ι → α) × (ι → β)) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun f i := (f.1 i, f.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

def factorTape (positions : Positions) :
    FullTape ≃ (DigestTape × (OpenTape positions × HiddenTape positions)) :=
  (functionPairEquiv Index (BitVec 256) PrivateLeafKey).trans
    (Equiv.prodCongr (Equiv.refl DigestTape)
      (Equiv.piEquivPiSubtypeProd (· ∈ positions) (fun _ : Index => PrivateLeafKey)))

private def asTransport {α β : Type} (e : α ≃ β) : Transport α β :=
  ⟨e, e.symm, e.left_inv, e.right_inv⟩

/-- The same factorization applies to zero, partial, and complete openings.
In the reference game, the observer and base permutation completion may depend
on the first two tapes while the hidden tape is still an independent draw. -/
theorem separate_hidden_tape {α : Type} (positions : Positions)
    (next : DigestTape → OpenTape positions → HiddenTape positions → ProbComp α) :
    (do let tape ← $ᵗ FullTape
        let pieces := factorTape positions tape
        next pieces.1 pieces.2.1 pieces.2.2) =ᵈ
      (do let digests ← $ᵗ DigestTape
          let opened ← $ᵗ OpenTape positions
          let closed ← $ᵗ HiddenTape positions
          next digests opened closed) := by
  let nextParts : DigestTape × (OpenTape positions × HiddenTape positions) → ProbComp α :=
    fun part => next part.1 part.2.1 part.2.2
  have equivalent := (uniform_transport_bind (asTransport (factorTape positions).symm) nextParts).symm
  apply equivalent.trans
  rw [SampleableType.uniformSample_prod_eq_bind, SampleableType.uniformSample_prod_eq_bind]
  simp only [nextParts, bind_assoc, pure_bind]
  rfl

theorem uniform_tape_coordinate {ι α β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Nonempty α] [SampleableType α] (index : ι) (next : α → ProbComp β) :
    (do let tape ← $ᵗ (ι → α); next (tape index)) =ᵈ
      (do let value ← $ᵗ α; next value) := by
  let read : (ι → α) ≃ α × ({j : ι // j ≠ index} → α) :=
    Equiv.piSplitAt index (fun _ => α)
  have separated := (uniform_transport_bind (asTransport read.symm) (fun pair => next pair.1)).symm
  apply separated.trans
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro value
  let : MeasurableSpace β := ⊤
  exact EvalDistEq.of_evalDist_eq (evalDist_bind_const _ _)


end TwoPermutationPrototype.Sampling
