import CommitGolfCandidate.TwoPermutationHidingTape

namespace TwoPermutationPrototype.Sampling
open OracleComp

def PinnedTargetsDistinct {A B : Type} (target : B → Option A) : Prop :=
  ∀ a b c, target b = some a → target c = some a → b = c

noncomputable def pinnedDigestSource {A B : Type} (target : B → Option A) (a : A) : Option B := by
  classical
  exact if existsTarget : ∃ b, target b = some a then some (Classical.choose existsTarget) else none

theorem pinned_digest_source_iff {A B : Type} {target : B → Option A}
    (distinct : PinnedTargetsDistinct target) (a : A) (b : B) :
    pinnedDigestSource target a = some b ↔ target b = some a := by
  classical
  unfold pinnedDigestSource
  by_cases existsTarget : ∃ b, target b = some a
  · simp only [existsTarget, dite_true, Option.some.injEq]
    constructor
    · rintro rfl
      exact Classical.choose_spec existsTarget
    · exact fun hits => distinct a _ _ (Classical.choose_spec existsTarget) hits
  · simp only [existsTarget, dite_false]
    constructor
    · intro same
      cases same
    · exact fun found => False.elim (existsTarget ⟨b, found⟩)

noncomputable def pinnedSwapDigestIndex {A B : Type} (target : B → Option A) : A ⊕ B → A ⊕ B
  | .inl a => (pinnedDigestSource target a).elim (.inl a) Sum.inr
  | .inr b => (target b).elim (.inr b) Sum.inl

theorem pinned_swap_digest_index_involutive {A B : Type} (target : B → Option A)
    (distinct : PinnedTargetsDistinct target) : Function.Involutive (pinnedSwapDigestIndex target) := by
  intro point
  cases point with
  | inl a =>
    cases source : pinnedDigestSource target a with
    | none => simp [pinnedSwapDigestIndex, source]
    | some b => simp [pinnedSwapDigestIndex, source, (pinned_digest_source_iff distinct a b).mp source]
  | inr b =>
    cases chosen : target b with
    | none => simp [pinnedSwapDigestIndex, chosen]
    | some a => simp [pinnedSwapDigestIndex, chosen, (pinned_digest_source_iff distinct a b).mpr chosen]

abbrev PinnedDigestTape (A B : Type) := A ⊕ B → BitVec 256

noncomputable def pinnedSwapDigestTape {A B : Type} (target : B → Option A)
    (tape : PinnedDigestTape A B) : PinnedDigestTape A B :=
  tape ∘ pinnedSwapDigestIndex target

/-- The real hidden digest is read from the latent A row if the address is
already present, and from the new B row otherwise. -/
def pinnedReadDigest {A B : Type} (target : B → Option A) (tape : PinnedDigestTape A B) (b : B) :
    BitVec 256 :=
  (target b).elim (tape (.inr b)) (fun a => tape (.inl a))

theorem pinned_read_swapped_digest {A B : Type} (target : B → Option A)
    (distinct : PinnedTargetsDistinct target) (tape : PinnedDigestTape A B) (b : B) :
    pinnedReadDigest target (pinnedSwapDigestTape target tape) b = tape (.inr b) := by
  cases chosen : target b with
  | none => simp [pinnedReadDigest, pinnedSwapDigestTape, pinnedSwapDigestIndex, chosen]
  | some a =>
    simp [pinnedReadDigest, pinnedSwapDigestTape, pinnedSwapDigestIndex, chosen,
      (pinned_digest_source_iff distinct a b).mpr chosen]

@[instance_reducible] noncomputable def pinnedDigestSampler (A B : Type) [Fintype A] [Fintype B] :
    SampleableType (PinnedDigestTape A B) := by
  classical
  exact SampleableType.ofFintype _

/-- Reassign fresh digest coordinates to overlapped A rows. For every fixed
partial injection of B addresses, the updated tape remains exactly uniform. -/
theorem pinned_uniform_reassign_digests {A B Output : Type} [Fintype A] [Fintype B]
    (target : B → Option A) (distinct : PinnedTargetsDistinct target)
    (next : PinnedDigestTape A B → ProbComp Output) :
    (do let tape ← @uniformSample _ (pinnedDigestSampler A B)
        next (pinnedSwapDigestTape target tape)) =ᵈ
    (do let tape ← @uniformSample _ (pinnedDigestSampler A B)
        next tape) := by
  let : SampleableType (PinnedDigestTape A B) := pinnedDigestSampler A B
  have twice (tape : PinnedDigestTape A B) :
      pinnedSwapDigestTape target (pinnedSwapDigestTape target tape) = tape := by
    funext index
    exact congrArg tape (pinned_swap_digest_index_involutive target distinct index)
  let transport : Transport (PinnedDigestTape A B) (PinnedDigestTape A B) :=
    ⟨pinnedSwapDigestTape target, pinnedSwapDigestTape target, twice, twice⟩
  exact (uniform_transport_bind transport next).symm

noncomputable local instance pinnedLowFunctionSampler {A : Type} [Fintype A] :
    SampleableType (A → BitVec 256) := by
  classical
  exact SampleableType.ofFintype _

theorem pinned_uniform_digest_tape_split {A B Output : Type} [Fintype A] [Fintype B]
    (next : (A → BitVec 256) → (B → BitVec 256) → ProbComp Output) :
    (do let tape ← @uniformSample _ (pinnedDigestSampler A B)
        next (fun a => tape (.inl a)) (fun b => tape (.inr b))) =ᵈ
    (do let left ← @uniformSample _ (@pinnedLowFunctionSampler A inferInstance)
        let right ← @uniformSample _ (@pinnedLowFunctionSampler B inferInstance)
        next left right) := by
  let layout : Transport (PinnedDigestTape A B) ((A → BitVec 256) × (B → BitVec 256)) :=
    { toFun := fun tape => (fun a => tape (.inl a), fun b => tape (.inr b))
      invFun := fun tapes => Sum.elim tapes.1 tapes.2
      leftInverse := fun tape => by funext slot; cases slot <;> rfl
      rightInverse := fun _ => rfl }
  let : SampleableType (PinnedDigestTape A B) := pinnedDigestSampler A B
  apply (uniform_transport_bind layout (fun tape => next (fun a => tape (.inl a)) (fun b => tape (.inr b)))).trans
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  rfl

/-- After fixing the high-tail history and the opened B addresses, low bits
for the exposed rows and remaining latent first rows can be drawn separately. -/
theorem pinned_split_revealed_lows {A Output : Type} [Fintype A]
    (exposed : A → Prop) [DecidablePred exposed] (next : (A → BitVec 256) → ProbComp Output) :
    (($ᵗ (A → BitVec 256)) >>= next) =ᵈ
      (do let visible ← $ᵗ ({i : A // exposed i} → BitVec 256)
          let privateLow ← $ᵗ ({i : A // ¬exposed i} → BitVec 256)
          next (fun i => if revealed : exposed i then visible ⟨i, revealed⟩ else privateLow ⟨i, revealed⟩)) := by
  let split := Equiv.piEquivPiSubtypeProd exposed (fun _ : A => BitVec 256)
  apply (uniform_transport_bind ⟨split.toFun, split.invFun, split.left_inv, split.right_inv⟩ next).trans
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  rfl

end TwoPermutationPrototype.Sampling
