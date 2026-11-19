import CommitGolfCandidate.TwoPermutationHidingPlans
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fin.Tuple.Basic

/-! The sequential two-call proposal tape and the independent per-position
reply tables give the same distribution. The order is first then second per site. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp

abbrev ReplyPair := Block × Block

noncomputable local instance replyTableSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

def serializeReplyPairs (pairs : List ReplyPair) : List Block :=
  pairs.flatMap (fun pair => [pair.1, pair.2])

def transportOfEquiv {α β : Type} (equiv : α ≃ β) : Transport α β :=
  ⟨equiv, equiv.symm, equiv.left_inv, equiv.right_inv⟩

theorem uniform_fin_reply_tape {α : Type} (count : Nat) (next : List Block → ProbComp α) :
    (do let table ← $ᵗ (Fin count → ReplyPair)
        next (serializeReplyPairs (List.ofFn table))) =ᵈ
      (sampleProposalTape (2 * count) >>= next) := by
  induction count generalizing next with
  | zero =>
    simp only [List.ofFn_zero, serializeReplyPairs, List.flatMap_nil, sampleProposalTape, pure_bind]
    let : MeasurableSpace α := ⊤
    exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const _ _)
  | succ count ih =>
    let vec := Fin.consEquiv (fun _ : Fin (count + 1) => ReplyPair)
    apply (uniform_transport_bind (transportOfEquiv vec.symm)
      (fun table => next (serializeReplyPairs (List.ofFn table)))).trans
    rw [SampleableType.uniformSample_prod_eq_bind, SampleableType.uniformSample_prod_eq_bind]
    rw [Nat.mul_succ, show 2 * count + 2 = (2 * count + 1) + 1 by omega,
      sampleProposalTape, sampleProposalTape]
    simp only [bind_assoc, pure_bind]
    apply EvalDistEq.bind_right
    intro first
    apply EvalDistEq.bind_right
    intro second
    change (do let table ← $ᵗ (Fin count → ReplyPair)
               next (serializeReplyPairs (List.ofFn (Fin.cons (first, second) table)))) =ᵈ _
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, serializeReplyPairs, List.flatMap_cons,
      List.cons_append, List.nil_append]
    apply (ih (fun tape => next (first :: second :: tape))).trans
    rfl

theorem uniform_enum_reply_tape {ι α : Type} [Fintype ι] (indices : List ι) (distinct : indices.Nodup)
    (covers : ∀ i : ι, i ∈ indices) (next : List Block → ProbComp α) :
    (do let table ← $ᵗ (ι → ReplyPair)
        next (serializeReplyPairs (indices.map table))) =ᵈ
      (sampleProposalTape (2 * indices.length) >>= next) := by
  classical
  let numbering := List.Nodup.getEquivOfForallMemList indices distinct covers
  let tableEquiv : (ι → ReplyPair) ≃ (Fin indices.length → ReplyPair) :=
    Equiv.arrowCongr numbering.symm (Equiv.refl _)
  apply (uniform_transport_bind (transportOfEquiv tableEquiv)
    (fun table => next (serializeReplyPairs (indices.map table)))).trans
  apply (EvalDistEq.bind_right _ (fun table => ?_)).trans (uniform_fin_reply_tape indices.length next)
  have same : indices.map (tableEquiv.symm table) = List.ofFn table := by
    calc
      _ = (List.ofFn indices.get).map (tableEquiv.symm table) :=
        congrArg (List.map (tableEquiv.symm table)) (List.ofFn_get indices).symm
      _ = _ := by
        rw [List.map_ofFn]
        congr 1
        funext i
        change table (numbering.symm (indices.get i)) = table i
        exact congrArg table (numbering.symm_apply_apply i)
  change next (serializeReplyPairs (indices.map (tableEquiv.symm table))) =ᵈ
    next (serializeReplyPairs (List.ofFn table))
  rw [same]


abbrev RawLeafTape (positions : Positions) := HiddenIndex positions → BitVec 128 × ReplyPair
abbrev UnopenedDigestTape (positions : Positions) := HiddenIndex positions → BitVec 256

def splitLeafKey : (BitVec 128 × ReplyPair) ≃ (BitVec 256 × PrivateLeafKey) where
  toFun raw := (outputDigest raw.2.2, raw.1, raw.2.1, raw.2.2.extractLsb' 256 1344)
  invFun separated := (separated.2.1, separated.2.2.1, separated.2.2.2 ++ separated.1)
  left_inv raw := by
    obtain ⟨salt, first, second⟩ := raw
    change (salt, first, second.extractLsb' 256 1344 ++ second.extractLsb' 0 256) =
      (salt, first, second)
    have joined : second.extractLsb' 256 1344 ++ second.extractLsb' 0 256 = second :=
      BitVec.extractLsb'_append_extractLsb'
    exact congrArg (fun (last : Block) => (salt, first, last)) joined
  right_inv separated := by
    obtain ⟨digest, salt, first, tail⟩ := separated
    change ((tail ++ digest).extractLsb' 0 256, salt, first, (tail ++ digest).extractLsb' 256 1344) =
      (digest, salt, first, tail)
    rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]

def factorLeafReplies (positions : Positions) :
    RawLeafTape positions ≃ (UnopenedDigestTape positions × HiddenTape positions) :=
  (Equiv.piCongrRight (fun _ : HiddenIndex positions => splitLeafKey)).trans
    (functionPairEquiv (HiddenIndex positions) (BitVec 256) PrivateLeafKey)

/-- Exposing the low 256 bits of every unopened second reply leaves the remaining
honest tape uniform and independent, even for an empty set of unopened sites. -/
theorem expose_unopened_digests {α : Type} (positions : Positions)
    (next : UnopenedDigestTape positions → HiddenTape positions → ProbComp α) :
    (do let raw ← $ᵗ RawLeafTape positions
        let separate := factorLeafReplies positions raw
        next separate.1 separate.2) =ᵈ
      (do let digests ← $ᵗ UnopenedDigestTape positions
          let hidden ← sampleHiddenTape positions
          next digests hidden) := by
  have transport := (uniform_transport_bind (transportOfEquiv (factorLeafReplies positions).symm)
    (fun pair => next pair.1 pair.2)).symm
  refine transport.trans ?_
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  rfl

end TwoPermutationPrototype.Sampling
