import CommitGolfCandidate.S3PermTwoCall

/-!
# The union bound with the unary term charged to inverse queries only

`prob_not_good_le` charges the unary bad event (`BadSpec.single`) to every query. For the two-call
leaf hash the unary event is "a fresh inverse answer is a valid first-call input", which a forward
query can never cause. `Strat.IQB st n` says that `st` makes at most `n` inverse queries on every
path; `prob_not_good_le_inv` then bounds

  Pr[ table not good and at most Q queries were made ] ≤ (Q (Q - 1) / 2 · k + n · u) / (|S| - Q),

so the forward queries of a long honest replay cost nothing in the unary term.
-/

set_option linter.unusedSectionVars false

namespace CommitGolfCandidate.Permutation

open Finset

variable {S : Type}

namespace Strat

variable {α β : Type}

/-- `IQB st n`: on every path `st` makes at most `n` inverse queries. -/
inductive IQB : Strat S α → ℕ → Prop
  | done (a : α) (n : ℕ) : IQB (.done a) n
  | fwd (x : S) (k : S → Strat S α) (n : ℕ) : (∀ y, IQB (k y) n) → IQB (.fwd x k) n
  | inv (y : S) (k : S → Strat S α) (n : ℕ) : (∀ x, IQB (k x) n) → IQB (.inv y k) (n + 1)
  | rand (m : ℕ) (k : Fin (m + 1) → Strat S α) (n : ℕ) : (∀ i, IQB (k i) n) → IQB (.rand m k) n

theorem IQB.mono {st : Strat S α} {n m : ℕ} (h : IQB st n) (hnm : n ≤ m) : IQB st m := by
  induction h generalizing m with
  | done a n => exact .done a m
  | fwd x k n _ ih => exact .fwd x k m fun y => ih y hnm
  | inv y k n _ ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .inv y k m fun x => ih x (by omega)
  | rand j k n _ ih => exact .rand j k m fun i => ih i hnm

theorem IQB.bind {st : Strat S α} {f : α → Strat S β} {n m : ℕ} (h : IQB st n)
    (hf : ∀ a, IQB (f a) m) : IQB (st.bind f) (n + m) := by
  induction h with
  | done a n => exact (hf a).mono (by omega)
  | fwd x k n _ ih => exact .fwd x _ _ ih
  | inv y k n _ ih =>
    have : n + 1 + m = (n + m) + 1 := by omega
    rw [this]
    exact .inv y _ _ ih
  | rand j k n _ ih => exact .rand j _ _ ih

/-- A bound on all queries is a bound on the inverse queries. -/
theorem QB.toIQB {st : Strat S α} {n : ℕ} (h : QB st n) : IQB st n := by
  induction h with
  | done a n => exact .done a n
  | fwd x k n _ ih => exact .fwd x k (n + 1) fun y => (ih y).mono (by omega)
  | inv y k n _ ih => exact .inv y k n ih
  | rand j k n _ ih => exact .rand j k n ih

end Strat

section Bound

variable [Fintype S] [DecidableEq S] {α : Type}

/-- The inductive form: from a good, well-formed state with `c` queries made, a strategy with at
most `n` inverse queries ends bad within `Q` queries with probability at most the pair budget
plus `n · u / (|S| - Q)`. -/
theorem exp_not_good_le_inv (B : BadSpec S) (k u Q : ℕ) (hQ : Q < Fintype.card S)
    (hFp : ∀ (x : S) (old : Entry S),
      ∃ F : Finset S, F.card ≤ k ∧ ∀ y, B.pair ⟨.fwd, x, y⟩ old → y ∈ F)
    (hFs : ∀ x y : S, ¬ B.single ⟨.fwd, x, y⟩)
    (hIp : ∀ (y : S) (old : Entry S),
      ∃ F : Finset S, F.card ≤ k ∧ ∀ x, B.pair ⟨.inv, x, y⟩ old → x ∈ F)
    (hIs : ∀ y : S, ∃ F : Finset S, F.card ≤ u ∧ ∀ x, B.single ⟨.inv, x, y⟩ → x ∈ F)
    (st : Strat S α) (n : ℕ) (hn : st.IQB n) (s : PState S) (hwf : s.trace.WF)
    (hlen : s.trace.length ≤ s.count) (hgood : B.Good s.trace) :
    st.exp s (fun _ s' => ind (¬ B.Good s'.trace ∧ s'.count ≤ Q)) ≤
      budget (Fintype.card S) k 0 Q s.count + (n : ℝ) * u / ((Fintype.card S : ℝ) - Q) := by
  have hD : (0 : ℝ) < (Fintype.card S : ℝ) - Q := by
    have : (Q : ℝ) < Fintype.card S := by exact_mod_cast hQ
    linarith
  have hU : ∀ m : ℕ, (0 : ℝ) ≤ (m : ℝ) * u / ((Fintype.card S : ℝ) - Q) := fun m =>
    div_nonneg (by positivity) hD.le
  have hR : ∀ (c m : ℕ), (0 : ℝ) ≤ budget (Fintype.card S) k 0 Q c +
      (m : ℝ) * u / ((Fintype.card S : ℝ) - Q) := fun c m =>
    add_nonneg (budget_nonneg hQ c) (hU m)
  induction hn generalizing s with
  | done a n =>
    simp only [Strat.exp]
    rw [ind_neg (fun h => h.1 hgood)]
    exact hR _ _
  | rand j kk n _ ih =>
    simp only [Strat.exp]
    exact avg_le (hR _ _) fun i _ => ih i s hwf hlen hgood
  | fwd x kk n _ ih =>
    obtain ⟨t, c⟩ := s
    simp only [Strat.exp] at *
    by_cases hc : c < Q
    swap
    · refine avg_le (hR _ _) fun y _ => ?_
      rw [Strat.exp_ind_count_gt (fun s' => ¬ B.Good s'.trace) Q (kk y) ⟨t.stepF x y, c + 1⟩
        (by show Q < c + 1; omega)]
      exact hR _ _
    by_cases hx : x ∈ t.usedIn
    · refine avg_le (hR _ _) fun y hy => ?_
      have hstep : t.stepF x y = t := by simp [Trace.stepF, hx]
      rw [hstep]
      have h1 := ih y ⟨t, c + 1⟩ hwf (by show t.length ≤ c + 1; omega) hgood
      have h2 := budget_succ_le (k := k) (u := 0) hQ c
      simp only at h1
      linarith
    · have hA : t.fwdAns x = t.freeOut := by simp [Trace.fwdAns, hx]
      rw [hA, budget_succ hc, add_assoc]
      have hF : ((Fintype.card S : ℝ) - Q) ≤ (t.freeOut.card : ℝ) := by
        rw [hwf.card_freeOut, Nat.cast_sub hwf.length_le]
        have : (t.length : ℝ) ≤ Q := by exact_mod_cast (by omega : t.length ≤ Q)
        linarith
      refine avg_step_le t.freeOut _ (fun y => ¬ B.Good (⟨.fwd, x, y⟩ :: t)) _ _ _ hD hF
        (by positivity) ?_ ?_
      · intro y hy
        have hstep : t.stepF x y = ⟨.fwd, x, y⟩ :: t := by simp [Trace.stepF, hx]
        rw [hstep]
        by_cases hg : B.Good (⟨.fwd, x, y⟩ :: t)
        · rw [ind_neg (not_not.2 hg), zero_add]
          exact ih y ⟨_, c + 1⟩ (hwf.cons hx (Trace.mem_freeOut.1 hy))
            (by show (⟨.fwd, x, y⟩ :: t).length ≤ c + 1; simp only [List.length_cons]; omega) hg
        · rw [ind_pos hg]
          have h1 := Strat.exp_le zero_le_one
            (fun (_ : α) (s' : PState S) => ind_le_one (¬ B.Good s'.trace ∧ s'.count ≤ Q))
            (kk y) ⟨⟨.fwd, x, y⟩ :: t, c + 1⟩
          have := hR (c + 1) n
          linarith
      · refine (sum_ind_bad_le B k 0 (fun y => ⟨.fwd, x, y⟩) (hFp x)
          ⟨∅, by simp, fun z hz => absurd hz (hFs x z)⟩ t hgood _).trans ?_
        push_cast
        have : (t.length : ℝ) ≤ c := by exact_mod_cast hlen
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  | inv y kk n _ ih =>
    obtain ⟨t, c⟩ := s
    simp only [Strat.exp] at *
    have hsplit : ((n + 1 : ℕ) : ℝ) * u / ((Fintype.card S : ℝ) - Q) =
        (u : ℝ) / ((Fintype.card S : ℝ) - Q) + (n : ℝ) * u / ((Fintype.card S : ℝ) - Q) := by
      push_cast
      ring
    by_cases hc : c < Q
    swap
    · refine avg_le (hR _ _) fun x _ => ?_
      rw [Strat.exp_ind_count_gt (fun s' => ¬ B.Good s'.trace) Q (kk x) ⟨t.stepI x y, c + 1⟩
        (by show Q < c + 1; omega)]
      exact hR _ _
    by_cases hy : y ∈ t.usedOut
    · refine avg_le (hR _ _) fun x hx => ?_
      have hstep : t.stepI x y = t := by simp [Trace.stepI, hy]
      rw [hstep]
      have h1 := ih x ⟨t, c + 1⟩ hwf (by show t.length ≤ c + 1; omega) hgood
      have h2 := budget_succ_le (k := k) (u := 0) hQ c
      have h3 : (0 : ℝ) ≤ (u : ℝ) / ((Fintype.card S : ℝ) - Q) := div_nonneg (by positivity) hD.le
      simp only at h1
      rw [hsplit]
      linarith
    · have hA : t.invAns y = t.freeIn := by simp [Trace.invAns, hy]
      have hF : ((Fintype.card S : ℝ) - Q) ≤ (t.freeIn.card : ℝ) := by
        rw [hwf.card_freeIn, Nat.cast_sub hwf.length_le]
        have : (t.length : ℝ) ≤ Q := by exact_mod_cast (by omega : t.length ≤ Q)
        linarith
      have hgoal : budget (Fintype.card S) k 0 Q c +
          ((n + 1 : ℕ) : ℝ) * u / ((Fintype.card S : ℝ) - Q) =
          ((c : ℝ) * k + u) / ((Fintype.card S : ℝ) - Q) +
            (budget (Fintype.card S) k 0 Q (c + 1) +
              (n : ℝ) * u / ((Fintype.card S : ℝ) - Q)) := by
        rw [budget_succ hc, hsplit]
        push_cast
        ring
      rw [hA, hgoal]
      refine avg_step_le t.freeIn _ (fun x => ¬ B.Good (⟨.inv, x, y⟩ :: t)) _ _ _ hD hF
        (by positivity) ?_ ?_
      · intro x hx
        have hstep : t.stepI x y = ⟨.inv, x, y⟩ :: t := by simp [Trace.stepI, hy]
        rw [hstep]
        by_cases hg : B.Good (⟨.inv, x, y⟩ :: t)
        · rw [ind_neg (not_not.2 hg), zero_add]
          exact ih x ⟨_, c + 1⟩ (hwf.cons (Trace.mem_freeIn.1 hx) hy)
            (by show (⟨.inv, x, y⟩ :: t).length ≤ c + 1; simp only [List.length_cons]; omega) hg
        · rw [ind_pos hg]
          have h1 := Strat.exp_le zero_le_one
            (fun (_ : α) (s' : PState S) => ind_le_one (¬ B.Good s'.trace ∧ s'.count ≤ Q))
            (kk x) ⟨⟨.inv, x, y⟩ :: t, c + 1⟩
          have := hR (c + 1) n
          linarith
      · refine (sum_ind_bad_le B k u (fun x => ⟨.inv, x, y⟩) (hIp y) (hIs y) t hgood _).trans ?_
        push_cast
        have : (t.length : ℝ) ≤ c := by exact_mod_cast hlen
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- **Union bound over queries, unary term on inverse queries only.** For every strategy with at
most `n` inverse queries on every path, the probability that the table is bad at the end while at
most `Q` queries were made is at most `(Q (Q - 1) / 2 · k + n · u) / (|S| - Q)`. -/
theorem prob_not_good_le_inv (B : BadSpec S) (k u Q : ℕ) (hQ : Q < Fintype.card S)
    (hFp : ∀ (x : S) (old : Entry S),
      ∃ F : Finset S, F.card ≤ k ∧ ∀ y, B.pair ⟨.fwd, x, y⟩ old → y ∈ F)
    (hFs : ∀ x y : S, ¬ B.single ⟨.fwd, x, y⟩)
    (hIp : ∀ (y : S) (old : Entry S),
      ∃ F : Finset S, F.card ≤ k ∧ ∀ x, B.pair ⟨.inv, x, y⟩ old → x ∈ F)
    (hIs : ∀ y : S, ∃ F : Finset S, F.card ≤ u ∧ ∀ x, B.single ⟨.inv, x, y⟩ → x ∈ F)
    (st : Strat S α) (n : ℕ) (hn : st.IQB n) :
    st.prob PState.init (fun _ s' => ¬ B.Good s'.trace ∧ s'.count ≤ Q) ≤
      ((Q : ℝ) * ((Q : ℝ) - 1) / 2 * k + (n : ℝ) * u) / ((Fintype.card S : ℝ) - Q) := by
  have h := exp_not_good_le_inv B k u Q hQ hFp hFs hIp hIs st n hn PState.init Trace.WF.nil
    (le_refl _) B.good_nil
  have hz : budget (Fintype.card S) k 0 Q (PState.init : PState S).count =
      ((Q : ℝ) * ((Q : ℝ) - 1) / 2 * k) / ((Fintype.card S : ℝ) - Q) := by
    show budget (Fintype.card S) k 0 Q 0 = _
    rw [budget_zero]
    simp
  rw [hz, ← add_div] at h
  exact h

end Bound

namespace TwoCall

variable [Fintype S] [DecidableEq S]
variable {X1 R C M2 D : Type} (H : TwoCall S X1 R C M2 D)

/-- The five bad events of the two-call leaf hash, with the unary event ("a fresh inverse answer
is a valid first-call input") charged only to the `n` inverse queries of the strategy. -/
theorem prob_bad_le_inv [Fintype X1] [Fintype R] [Fintype M2] [DecidableEq C] [DecidableEq D]
    {α : Type} (Kd Kc K2 V Q : ℕ) (hQ : Q < Fintype.card S)
    (hKd : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ Kd)
    (hKc : ∀ c : C, (univ.filter fun s => H.chop s = c).card ≤ Kc)
    (hK2 : Fintype.card R * Fintype.card M2 ≤ K2)
    (hV : Fintype.card X1 ≤ V) (st : Strat S α) (n : ℕ) (hn : st.IQB n) :
    st.prob PState.init (fun _ s' => H.Bad s'.trace ∧ s'.count ≤ Q) ≤
      ((Q : ℝ) * ((Q : ℝ) - 1) / 2 * (Kd + 2 * Kc + K2 : ℕ) + (n : ℝ) * V) /
        ((Fintype.card S : ℝ) - Q) := by
  classical
  have hmono : st.prob PState.init (fun _ s' => H.Bad s'.trace ∧ s'.count ≤ Q) ≤
      st.prob PState.init (fun _ s' => ¬ H.badSpec.Good s'.trace ∧ s'.count ≤ Q) :=
    Strat.exp_mono (fun _ s' => ind_mono fun h => ⟨(H.not_good_iff _).2 h.1, h.2⟩) st _
  refine hmono.trans (prob_not_good_le_inv H.badSpec (Kd + 2 * Kc + K2) V Q hQ ?_ ?_ ?_ ?_ st n hn)
  · intro x old
    refine ⟨(univ.filter fun s => H.trunc s = H.trunc old.out) ∪
      (univ.filter fun s => H.chop s = H.chop old.out) ∪
      (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop s, m)), ?_, ?_⟩
    · have h3 : (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop s, m)).card ≤ Kc := by
        rcases (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop s, m)).eq_empty_or_nonempty
          with h0 | ⟨y0, hy0⟩
        · rw [h0]
          exact Nat.zero_le _
        · obtain ⟨r0, m0, h0⟩ := (Finset.mem_filter.1 hy0).2
          refine (Finset.card_le_card fun y hy => ?_).trans (hKc (H.chop y0))
          obtain ⟨r, m, h⟩ := (Finset.mem_filter.1 hy).2
          have hinj := H.enc2_inj (h.symm.trans h0)
          simp only [Prod.mk.injEq] at hinj
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hinj.2.1⟩
      have := hKd (H.trunc old.out)
      have := hKc (H.chop old.out)
      have h12 := Finset.card_union_le (univ.filter fun s => H.trunc s = H.trunc old.out)
        (univ.filter fun s => H.chop s = H.chop old.out)
      have h123 := Finset.card_union_le
        ((univ.filter fun s => H.trunc s = H.trunc old.out) ∪
          (univ.filter fun s => H.chop s = H.chop old.out))
        (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop s, m))
      omega
    · intro y hy
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hy with h | h | h | h
      · exact Or.inl (Or.inl h.2)
      · exact Or.inl (Or.inr h.2)
      · exact absurd h.1 (by simp)
      · exact Or.inr h.2
  · intro x y hs
    exact absurd hs.1 (by simp)
  · intro y old
    refine ⟨univ.image fun p : R × M2 => H.enc2 (p.1, H.chop old.out, p.2), ?_, ?_⟩
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_univ, Fintype.card_prod]
      omega
    · intro x hx
      rcases hx with h | h | h | h
      · exact absurd h.1 (by simp)
      · exact absurd h.1 (by simp)
      · obtain ⟨r, m, h⟩ := h.2
        exact Finset.mem_image.2 ⟨(r, m), Finset.mem_univ _, h.symm⟩
      · exact absurd h.1 (by simp)
  · intro y
    refine ⟨univ.image H.enc1, Finset.card_image_le.trans (by simpa using hV), fun x hx => ?_⟩
    obtain ⟨x0, h0⟩ := hx.2
    exact Finset.mem_image.2 ⟨x0, Finset.mem_univ _, h0⟩

theorem eval_IQB (i : X1 × R × M2) : (H.eval i).IQB 0 :=
  .fwd _ _ 0 fun _ => .fwd _ _ 0 fun _ => .done _ 0

end TwoCall

end CommitGolfCandidate.Permutation
