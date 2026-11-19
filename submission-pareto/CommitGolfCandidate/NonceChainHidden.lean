import CommitGolfCandidate.S3PermModel
import Mathlib.Logic.Equiv.Prod

/-! A public transcript can use all the disclosed prefixes. Conditional on those
prefixes, the hidden suffix of each ideal vertex is an independent uniform key.
The initial vertex may encode its key differently from every reply. -/
namespace CommitGolfCandidate.Permutation.NonceChain
open Finset
set_option linter.unusedSectionVars false

variable {I K S A D : Type}

noncomputable abbrev mean {X : Type} [Fintype X] (f : X → ℝ) := avg univ f

theorem mean_equiv [Fintype A] [Fintype D] (e : A ≃ D) (f : D → ℝ) :
    mean (fun x => f (e x)) = mean f := by
  unfold mean avg
  rw [Finset.card_univ, Finset.card_univ, Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ fun _ => rfl

theorem mean_prod [Fintype A] [Fintype D] (f : A → D → ℝ) :
    mean (fun p : A × D => f p.1 p.2) = mean (fun a => mean (f a)) := by
  unfold mean avg
  simp only [Finset.card_univ, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← Finset.sum_div, div_div, mul_comm (Fintype.card D : ℝ)]

private theorem key_hit [Fintype K] [DecidableEq S] (e : K → S) (inj : Function.Injective e)
    (seen : Finset S) :
    mean (fun k => ind (e k ∈ seen)) ≤ seen.card / (Fintype.card K : ℝ) := by
  classical
  unfold mean avg
  rw [sum_ind, Finset.card_univ]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  norm_cast
  apply Finset.card_le_card_of_injOn e _ inj.injOn
  intro k hk
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exact hk

def Exposed [DecidableEq S] [Fintype I] (v : I → S) (seen : Finset S) : Prop :=
  ∃ i, v i ∈ seen ∨ ∃ j, j ≠ i ∧ v i = v j

/-- The conditional probability of touching any of the fixed transcript endpoints
or of repeating a vertex. Each encoding is injective in that vertex's private key. -/
theorem exposed_bound [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq S]
    [Nonempty K] (encode : I → K → S) (inj : ∀ i, Function.Injective (encode i))
    (seen : Finset S) :
    mean (fun h : I → K => ind (Exposed (fun i => encode i (h i)) seen)) ≤
      (Fintype.card I : ℝ) * ((seen.card + Fintype.card I : ℝ) / Fintype.card K) := by
  classical
  let hit (i : I) (h : I → K) := encode i (h i) ∈ seen ∨
    ∃ j, j ≠ i ∧ encode i (h i) = encode j (h j)
  have single (i : I) : mean (fun h => ind (hit i h)) ≤
      (seen.card + Fintype.card I : ℝ) / Fintype.card K := by
    let split := (Equiv.funSplitAt i K).trans (Equiv.prodComm ..)
    let rest := { j : I // j ≠ i }
    let payoff (r : rest → K) (k : K) := ind (hit i (split.symm (r, k)))
    have equiv := mean_equiv split (fun p => payoff p.1 p.2)
    have repr : mean (fun h => ind (hit i h)) = mean (fun r => mean (payoff r)) := by
      rw [← mean_prod, ← equiv]
      apply avg_congr
      intro h _
      change ind (hit i h) = ind (hit i (split.symm (split h)))
      rw [split.symm_apply_apply]
    rw [repr]
    apply avg_le (by positivity)
    intro r _
    let others := univ.image (fun j : rest => encode j.val (r j))
    have inside (k : K) : hit i (split.symm (r,k)) → encode i k ∈ seen ∪ others := by
      intro h
      change (encode i _ ∈ seen ∨ ∃ j, j ≠ i ∧ encode i _ = encode j _) at h
      rcases h with h | ⟨j, ne, h⟩
      · exact Finset.mem_union_left _ (by simpa [split, Equiv.funSplitAt, Equiv.piSplitAt] using h)
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨⟨j,ne⟩, Finset.mem_univ _, by
          simpa [split, Equiv.funSplitAt, Equiv.piSplitAt,ne] using h.symm⟩
    have size : (seen ∪ others).card ≤ seen.card + Fintype.card I := by
      apply (Finset.card_union_le _ _).trans
      exact Nat.add_le_add_left ((Finset.card_image_le.trans (by
        rw [Finset.card_univ]
        exact Fintype.card_subtype_le _))) _
    exact (avg_mono (fun k _ => ind_mono (inside k))).trans
      ((key_hit (encode i) (inj i) _).trans (div_le_div_of_nonneg_right
        (by exact_mod_cast size) (Nat.cast_nonneg _)))
  have union (h : I → K) :
      ind (Exposed (fun i => encode i (h i)) seen) ≤ ∑ i, ind (hit i h) := by
    by_cases bad : Exposed (fun i => encode i (h i)) seen
    · obtain ⟨i, hi⟩ := bad
      exact (ind_le_one _).trans ((ind_pos (show hit i h from hi)) ▸
        (Finset.single_le_sum (f := fun i => ind (hit i h)) (fun j _ => ind_nonneg _) (mem_univ i)))
    · rw [ind_neg bad]
      exact Finset.sum_nonneg fun _ _ => ind_nonneg _
  refine (avg_mono (fun h _ => union h)).trans ?_
  rw [avg_sum]
  exact (Finset.sum_le_sum fun i _ => single i).trans_eq (by simp)

end CommitGolfCandidate.Permutation.NonceChain
