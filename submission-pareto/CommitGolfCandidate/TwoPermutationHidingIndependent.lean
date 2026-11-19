import CommitGolfCandidate.TwoPermutationHidingAlignment

/-! Translate the proposal sequence to a common public digest tape and the
independent secrets used by the adaptive observer bound. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp
set_option maxRecDepth 8192

noncomputable local instance independentFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

abbrev UnopenedSalts (positions : Positions) := HiddenIndex positions → BitVec 128
abbrev OpenedDigests (positions : Positions) := {i : Index // i ∈ positions} → BitVec 256

def fullDigestTape {positions : Positions} (opened : OpenedDigests positions)
    (closed : UnopenedDigestTape positions) : DigestTape :=
  fun index => if selected : index ∈ positions then opened ⟨index, selected⟩ else closed ⟨index, selected⟩

def publicSaltTape {positions : Positions} (salts : UnopenedSalts positions) (index : Index) : BitVec 128 :=
  if closed : index ∉ positions then salts ⟨index, closed⟩ else 0

theorem independent_honest_proposals {α : Type} (positions : Positions) (opened : OpenedDigests positions)
    (next : (Index → BitVec 128) → List Block → ProbComp α) :
    (do let salts ← $ᵗ UnopenedSalts positions
        let tape ← sampleProposalTape (2 * (hiddenIndices positions).length)
        next (publicSaltTape salts) tape) =ᵈ
      (do let digests ← $ᵗ UnopenedDigestTape positions
          let hidden ← sampleHiddenTape positions
          let replies := hiddenReplyPairs (fullDigestTape opened digests) hidden
          next (hiddenSalts hidden) (serializeReplyPairs ((hiddenIndices positions).map replies))) := by
  classical
  let indices := hiddenIndices positions
  let paired (salts : UnopenedSalts positions) (replies : HiddenIndex positions → ReplyPair) :=
    next (publicSaltTape salts) (serializeReplyPairs (indices.map replies))
  trans (do let salts ← $ᵗ UnopenedSalts positions
            let replies ← $ᵗ (HiddenIndex positions → ReplyPair)
            paired salts replies)
  · apply EvalDistEq.bind_right
    intro salts
    exact (uniform_enum_reply_tape indices (Finset.nodup_toList _)
      (fun i => by simp [indices, hiddenIndices]) (next (publicSaltTape salts))).symm
  · let combine := functionPairEquiv (HiddenIndex positions) (BitVec 128) ReplyPair
    trans (do let raw ← $ᵗ RawLeafTape positions
              paired (combine raw).1 (combine raw).2)
    · have same := uniform_transport_bind (transportOfEquiv combine.symm)
        (fun pair => paired pair.1 pair.2)
      rw [SampleableType.uniformSample_prod_eq_bind] at same
      simp only [bind_assoc, pure_bind] at same
      exact same
    · let fromSecret (digests : UnopenedDigestTape positions) (hidden : HiddenTape positions) :=
        next (hiddenSalts hidden) (serializeReplyPairs
          (indices.map (hiddenReplyPairs (fullDigestTape opened digests) hidden)))
      trans (do let raw ← $ᵗ RawLeafTape positions
                let pieces := factorLeafReplies positions raw
                fromSecret pieces.1 pieces.2)
      · apply EvalDistEq.bind_right
        intro raw
        dsimp only [paired, fromSecret]
        have sameSalts : publicSaltTape (combine raw).1 = hiddenSalts (factorLeafReplies positions raw).2 := by
          funext i
          unfold publicSaltTape hiddenSalts
          split <;> rfl
        have sameReplies : (combine raw).2 =
            hiddenReplyPairs (fullDigestTape opened (factorLeafReplies positions raw).1)
              (factorLeafReplies positions raw).2 := by
          funext i
          have closed := i.property
          simp only [hiddenReplyPairs, fullDigestTape, closed, dite_false]
          change ((raw i).2.1, (raw i).2.2) =
            ((raw i).2.1, (raw i).2.2.extractLsb' 256 1344 ++ (raw i).2.2.extractLsb' 0 256)
          have joined : (raw i).2.2.extractLsb' 256 1344 ++ (raw i).2.2.extractLsb' 0 256 = (raw i).2.2 :=
            BitVec.extractLsb'_append_extractLsb'
          exact congrArg (fun (last : Block) => ((raw i).2.1, last)) joined.symm
        rw [sameSalts, sameReplies]
      · exact expose_unopened_digests positions fromSecret


theorem hidden_index_count (positions : Positions) :
    (hiddenIndices positions).length + positions.card = 2 ^ 24 := by
  have total : Fintype.card Index = 2 ^ 24 := Fintype.card_fin _
  have count := Fintype.card_subtype_compl (fun index : Index => index ∈ positions)
  simp only [Fintype.card_coe, total] at count
  have bound : positions.card ≤ 2 ^ 24 := by simpa only [total] using Finset.card_le_univ positions
  rw [hiddenIndices, Finset.length_toList, Finset.card_univ]
  change Fintype.card {i : Index // i ∉ positions} + positions.card = _
  rw [count]
  omega

noncomputable def unopenedPlans (positions : Positions) (messages : Index → Words 32)
    (salts : Index → BitVec 128) : List InputPlan :=
  leafPlans messages salts ((hiddenIndices positions).map Subtype.val)

open MeasureTheory in
theorem honest_proposal_conflict_le {positions : Positions} (cache : Cache) (messages : Index → Words 32)
    (openedDigests : OpenedDigests positions) (firstStage openedRows : List Row) (budget : Nat)
    (seed : cache.entries = openedRows ++ firstStage) (firstCount : firstStage.length ≤ budget)
    (openedCount : openedRows.length ≤ 2 * positions.card)
    (tags : ∀ row ∈ openedRows, exposedInputTag positions row.1) :
    Pr{let flag ← (($ᵗ UnopenedSalts positions) >>= fun salts =>
      proposedConflict cache [] (unopenedPlans positions messages (publicSaltTape salts)))}[
      flag = true] ≤
      (budget : ENNReal) * hiddenPairRate + (2 ^ 25 : ENNReal) * (((budget : ENNReal) + 2 ^ 25) / 2 ^ 1600) := by
  classical
  let indices := hiddenIndices positions
  let count := 2 * indices.length
  let plan (salts : Index → BitVec 128) := unopenedPlans positions messages salts
  let input (salts : Index → BitVec 128) := plannedInputHit cache.entries [] (plan salts)
  let outputAllowance := (2 ^ 25 : ENNReal) * (((budget : ENNReal) + 2 ^ 25) / 2 ^ 1600)
  have lengthOf (salts : Index → BitVec 128) : (plan salts).length = count := by
    simp [plan, count, indices, unopenedPlans, leaf_plans_length]
  have total := hidden_index_count positions
  have plansBound : count ≤ 2 ^ 25 := by dsimp [count, indices]; omega
  have withReplies : cache.entries.length + count ≤ budget + 2 ^ 25 := by
    rw [seed, List.length_append]
    dsimp [count, indices]
    omega
  have outputBound (salts : Index → BitVec 128) :
      ((plan salts).length : ENNReal) * (((cache.entries.length + (plan salts).length : Nat) : ENNReal) / 2 ^ 1600) ≤
        outputAllowance := by
    rw [lengthOf]
    unfold outputAllowance
    apply mul_le_mul
    · exact_mod_cast plansBound
    · apply ENNReal.div_le_div_right
      exact_mod_cast withReplies
    · exact zero_le
    · exact zero_le
  have nodup : (indices.map (Subtype.val : HiddenIndex positions → Index)).Nodup :=
    (Finset.nodup_toList _).map Subtype.val_injective
  have bound (salts : UnopenedSalts positions) :
      Pr{let flag ← proposedConflict cache [] (plan (publicSaltTape salts))}[flag = true] ≤
        outputAllowance + Pr{let tape ← sampleProposalTape count}[input (publicSaltTape salts) tape] := by
    have proposed := proposal_conflict_decompose cache [] (plan (publicSaltTape salts))
      (fun tape possible => leaf_plan_inputs_distinct messages _ _ nodup [] tape possible)
    refine proposed.trans ((add_le_add ?_ (outputBound _)).trans_eq (add_comm _ _))
    rw [lengthOf]
  rw [prEvent_bind_eq_tsum]
  refine (tsum_prEvent_mul_le_add_of_le ($ᵗ UnopenedSalts positions) bound).trans ?_
  have inputDist :=
    (independent_honest_proposals positions openedDigests (fun salts tape => pure (input salts tape))).prEvent_eq id
  have prefixEvent :
      (∑' salts, Pr{let y ← $ᵗ UnopenedSalts positions}[y = salts] *
        Pr{let tape ← sampleProposalTape count}[input (publicSaltTape salts) tape]) ≤
          (budget : ENNReal) * hiddenPairRate := by
    have translated : (∑' salts, Pr{let y ← $ᵗ UnopenedSalts positions}[y = salts] *
        Pr{let tape ← sampleProposalTape count}[input (publicSaltTape salts) tape]) =
        Pr{let event ← (do let salts ← $ᵗ UnopenedSalts positions
                            let tape ← sampleProposalTape count
                            pure (input (publicSaltTape salts) tape))}[id event] := by
      rw [prEvent_bind_eq_tsum]
      simp only [bind_pure_comp, prEvent_map, id_eq]
    rw [translated, inputDist]
    apply prEvent_bind_le_of_forall_le_of_support
    intro closed _
    have each := ideal_first_stage_hit_le (fullDigestTape openedDigests closed) messages firstStage openedRows tags
    have castFirst : (firstStage.length : ENNReal) ≤ (budget : ENNReal) := by exact_mod_cast firstCount
    have cost := each.trans (mul_le_mul_of_nonneg_right castFirst zero_le)
    simp only [bind_pure_comp, prEvent_map, id_eq]
    simpa [input, plan, unopenedPlans, seed, indices] using cost
  exact (add_le_add le_rfl prefixEvent).trans_eq (add_comm _ _)

end TwoPermutationPrototype.Sampling
