import CommitGolfCandidate.S3PermModel

/-!
# The union bound over queries for bad events of the lazy permutation

A bad event is described by a `BadSpec`: a relation `pair new old` between a table entry and an
older one, and a predicate `single` on one entry. A table is `Good` when no entry is `single`-bad
and no entry is `pair`-bad with an older entry.

`prob_not_good_le` is the generic bound: if for every fresh query at most `k` answers are
`pair`-bad with any one older entry and at most `u` answers are `single`-bad, then for every
strategy, whatever its number of queries,

  Pr[ table not good and at most Q queries were made ] ≤ (Q (Q - 1) / 2 · k + Q · u) / (|S| - Q).
-/

set_option linter.unusedSectionVars false

namespace CommitGolfCandidate.Permutation

open Finset

variable {S : Type}

/-- A family of bad events on tables, see the file header. -/
structure BadSpec (S : Type) where
  /-- `pair new old`: the entry `new` is in a forbidden relation with the older entry `old`. -/
  pair : Entry S → Entry S → Prop
  /-- `single e`: the entry `e` is forbidden by itself. -/
  single : Entry S → Prop

namespace BadSpec

/-- No bad event has happened in the table `t`. -/
def Good (B : BadSpec S) (t : Trace S) : Prop :=
  t.Pairwise (fun new old => ¬ B.pair new old) ∧ ∀ e ∈ t, ¬ B.single e

theorem good_nil (B : BadSpec S) : B.Good [] := ⟨List.Pairwise.nil, by simp⟩

theorem good_cons_iff (B : BadSpec S) (e : Entry S) (t : Trace S) :
    B.Good (e :: t) ↔ (∀ old ∈ t, ¬ B.pair e old) ∧ ¬ B.single e ∧ B.Good t := by
  unfold Good
  rw [List.pairwise_cons]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h3 e List.mem_cons_self, h2, fun e' he' => h3 e' (List.mem_cons_of_mem _ he')⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, h3⟩, fun e' he' => ?_⟩
    rcases List.mem_cons.1 he' with rfl | h
    · exact h2
    · exact h4 e' h

/-- In a good table, of two different entries the newer one is not `pair`-bad with the older
one; without knowing which is newer, the relation fails in at least one of the two orders. -/
theorem Good.not_pair {B : BadSpec S} {t : Trace S} (h : B.Good t) {e e' : Entry S}
    (he : e ∈ t) (he' : e' ∈ t) (hne : e ≠ e') : ¬ B.pair e e' ∨ ¬ B.pair e' e := by
  have hp := h.1
  clear h
  induction t with
  | nil => simp at he
  | cons a t ih =>
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 he with rfl | he1
    · rcases List.mem_cons.1 he' with rfl | he1'
      · exact absurd rfl hne
      · exact Or.inl (hp.1 _ he1')
    · rcases List.mem_cons.1 he' with rfl | he1'
      · exact Or.inr (hp.1 _ he1)
      · exact ih he1 he1' hp.2

theorem Good.not_single {B : BadSpec S} {t : Trace S} (h : B.Good t) {e : Entry S}
    (he : e ∈ t) : ¬ B.single e := h.2 e he

end BadSpec

namespace Strat

variable [Fintype S] [DecidableEq S] {α : Type}

theorem post_count (st : Strat S α) (s : PState S) :
    st.post s fun _ s' => s.count ≤ s'.count := by
  induction st generalizing s with
  | done a => exact le_refl _
  | fwd x k ih =>
    exact fun y _ => post_mono (fun a s' h => by simp only at h; omega) (ih y _)
  | inv y k ih =>
    exact fun x _ => post_mono (fun a s' h => by simp only at h; omega) (ih x _)
  | rand n k ih => exact fun i => ih i s

/-- Once more than `Q` queries were made, an event that requires `count ≤ Q` is impossible. -/
theorem exp_ind_count_gt (P : PState S → Prop) (Q : ℕ) (st : Strat S α) (s : PState S)
    (hs : Q < s.count) :
    st.exp s (fun _ s' => ind (P s' ∧ s'.count ≤ Q)) = 0 := by
  rw [exp_congr_of_post (post_count st s) (g := fun _ _ => 0), exp_zero]
  intro a s' h
  exact ind_neg fun h' => by omega

end Strat

section Bound

variable [Fintype S] [DecidableEq S] {α : Type}

/-- At most `|t| · k + u` answers to a fresh query make a good table bad (`mk` builds the new
entry from the answer; it is used with `mk y = ⟨.fwd, x, y⟩` and `mk x = ⟨.inv, x, y⟩`). -/
theorem sum_ind_bad_le (B : BadSpec S) (k u : ℕ) (mk : S → Entry S)
    (hp : ∀ old : Entry S, ∃ F : Finset S, F.card ≤ k ∧ ∀ z, B.pair (mk z) old → z ∈ F)
    (hs : ∃ F : Finset S, F.card ≤ u ∧ ∀ z, B.single (mk z) → z ∈ F)
    (t : Trace S) (ht : B.Good t) (A : Finset S) :
    ∑ z ∈ A, ind (¬ B.Good (mk z :: t)) ≤ ((t.length * k + u : ℕ) : ℝ) := by
  choose Fp hFp1 hFp2 using hp
  obtain ⟨Fs, hFs1, hFs2⟩ := hs
  refine (sum_ind_le A ((t.toFinset.biUnion Fp) ∪ Fs) _ ?_).trans ?_
  · intro z _ hz
    rw [B.good_cons_iff] at hz
    simp only [ht, and_true, not_and_or, not_forall, not_not] at hz
    rw [Finset.mem_union, Finset.mem_biUnion]
    rcases hz with ⟨old, hold, hpair⟩ | hsingle
    · exact Or.inl ⟨old, List.mem_toFinset.2 hold, hFp2 old z (by simpa using hpair)⟩
    · exact Or.inr (hFs2 z hsingle)
  · have h1 : ((t.toFinset.biUnion Fp) ∪ Fs).card ≤ t.length * k + u :=
      calc ((t.toFinset.biUnion Fp) ∪ Fs).card
          ≤ (t.toFinset.biUnion Fp).card + Fs.card := Finset.card_union_le _ _
        _ ≤ t.toFinset.card * k + u :=
            Nat.add_le_add (Finset.card_biUnion_le_card_mul _ _ _ fun old _ => hFp1 old) hFs1
        _ ≤ t.length * k + u :=
            Nat.add_le_add_right (Nat.mul_le_mul_right _ (List.toFinset_card_le t)) _
    exact_mod_cast h1

/-- The remaining budget of the union bound when `c` queries have been made. -/
noncomputable def budget (card : ℕ) (k u Q c : ℕ) : ℝ :=
  (∑ i ∈ Finset.Ico c Q, ((i : ℝ) * k + u)) / ((card : ℝ) - Q)

theorem budget_nonneg {card k u Q : ℕ} (hQ : Q < card) (c : ℕ) : 0 ≤ budget card k u Q c := by
  unfold budget
  have hD : (0 : ℝ) < (card : ℝ) - Q := by
    have : (Q : ℝ) < card := by exact_mod_cast hQ
    linarith
  exact div_nonneg (Finset.sum_nonneg fun i _ => by positivity) hD.le

theorem budget_succ {card k u Q c : ℕ} (hc : c < Q) :
    budget card k u Q c = ((c : ℝ) * k + u) / ((card : ℝ) - Q) + budget card k u Q (c + 1) := by
  unfold budget
  rw [Finset.sum_eq_sum_Ico_succ_bot hc, add_div]

theorem budget_succ_le {card k u Q : ℕ} (hQ : Q < card) (c : ℕ) :
    budget card k u Q (c + 1) ≤ budget card k u Q c := by
  by_cases hc : c < Q
  · rw [budget_succ hc]
    have hD : (0 : ℝ) < (card : ℝ) - Q := by
      have : (Q : ℝ) < card := by exact_mod_cast hQ
      linarith
    have : 0 ≤ ((c : ℝ) * k + u) / ((card : ℝ) - Q) := div_nonneg (by positivity) hD.le
    linarith
  · unfold budget
    rw [Finset.Ico_eq_empty (by omega), Finset.Ico_eq_empty (by omega)]

/-- One fresh query: if each answer `z ∈ A` leads to a continuation worth at most
`ind (bad z) + R`, and the bad answers number at most `β`, the average is at most `β / D + R`
for any `0 < D ≤ |A|`. -/
theorem avg_step_le (A : Finset S) (g : S → ℝ) (bad : S → Prop) (R β D : ℝ)
    (hD : 0 < D) (hDA : D ≤ (A.card : ℝ)) (hβ : 0 ≤ β)
    (hg : ∀ z ∈ A, g z ≤ ind (bad z) + R) (hbad : ∑ z ∈ A, ind (bad z) ≤ β) :
    avg A g ≤ β / D + R := by
  have hne : A.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < A.card := lt_of_lt_of_le hD hDA
    exact_mod_cast this
  refine (avg_mono hg).trans ?_
  rw [avg_add, avg_const hne]
  refine add_le_add ?_ (le_refl _)
  unfold avg
  exact div_le_div₀ hβ hbad hD hDA

/-- The inductive form of the union bound: from a good, well-formed state with `c` queries made,
the probability of ending bad within `Q` queries is at most the remaining budget. -/
theorem exp_not_good_le (B : BadSpec S) (k u Q : ℕ) (hQ : Q < Fintype.card S)
    (hFp : ∀ (x : S) (old : Entry S),
      ∃ F : Finset S, F.card ≤ k ∧ ∀ y, B.pair ⟨.fwd, x, y⟩ old → y ∈ F)
    (hFs : ∀ x : S, ∃ F : Finset S, F.card ≤ u ∧ ∀ y, B.single ⟨.fwd, x, y⟩ → y ∈ F)
    (hIp : ∀ (y : S) (old : Entry S),
      ∃ F : Finset S, F.card ≤ k ∧ ∀ x, B.pair ⟨.inv, x, y⟩ old → x ∈ F)
    (hIs : ∀ y : S, ∃ F : Finset S, F.card ≤ u ∧ ∀ x, B.single ⟨.inv, x, y⟩ → x ∈ F)
    (st : Strat S α) (s : PState S) (hwf : s.trace.WF) (hlen : s.trace.length ≤ s.count)
    (hgood : B.Good s.trace) :
    st.exp s (fun _ s' => ind (¬ B.Good s'.trace ∧ s'.count ≤ Q)) ≤
      budget (Fintype.card S) k u Q s.count := by
  have hD : (0 : ℝ) < (Fintype.card S : ℝ) - Q := by
    have : (Q : ℝ) < Fintype.card S := by exact_mod_cast hQ
    linarith
  induction st generalizing s with
  | done a =>
    simp only [Strat.exp]
    rw [ind_neg (fun h => h.1 hgood)]
    exact budget_nonneg hQ _
  | rand n kk ih =>
    simp only [Strat.exp]
    exact avg_le (budget_nonneg hQ _) fun i _ => ih i s hwf hlen hgood
  | fwd x kk ih =>
    obtain ⟨t, c⟩ := s
    simp only [Strat.exp] at *
    by_cases hc : c < Q
    swap
    · refine avg_le (budget_nonneg hQ _) fun y _ => ?_
      rw [Strat.exp_ind_count_gt (fun s' => ¬ B.Good s'.trace) Q (kk y) ⟨t.stepF x y, c + 1⟩
        (by show Q < c + 1; omega)]
      exact budget_nonneg hQ _
    by_cases hx : x ∈ t.usedIn
    · refine avg_le (budget_nonneg hQ _) fun y hy => ?_
      have hstep : t.stepF x y = t := by simp [Trace.stepF, hx]
      rw [hstep]
      exact (ih y ⟨t, c + 1⟩ hwf (by show t.length ≤ c + 1; omega) hgood).trans
        (budget_succ_le hQ c)
    · have hA : t.fwdAns x = t.freeOut := by simp [Trace.fwdAns, hx]
      rw [hA, budget_succ hc]
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
          have := budget_nonneg (k := k) (u := u) hQ (c + 1)
          linarith
      · refine (sum_ind_bad_le B k u (fun y => ⟨.fwd, x, y⟩) (hFp x) (hFs x) t hgood _).trans ?_
        push_cast
        have : (t.length : ℝ) ≤ c := by exact_mod_cast hlen
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  | inv y kk ih =>
    obtain ⟨t, c⟩ := s
    simp only [Strat.exp] at *
    by_cases hc : c < Q
    swap
    · refine avg_le (budget_nonneg hQ _) fun x _ => ?_
      rw [Strat.exp_ind_count_gt (fun s' => ¬ B.Good s'.trace) Q (kk x) ⟨t.stepI x y, c + 1⟩
        (by show Q < c + 1; omega)]
      exact budget_nonneg hQ _
    by_cases hy : y ∈ t.usedOut
    · refine avg_le (budget_nonneg hQ _) fun x hx => ?_
      have hstep : t.stepI x y = t := by simp [Trace.stepI, hy]
      rw [hstep]
      exact (ih x ⟨t, c + 1⟩ hwf (by show t.length ≤ c + 1; omega) hgood).trans
        (budget_succ_le hQ c)
    · have hA : t.invAns y = t.freeIn := by simp [Trace.invAns, hy]
      rw [hA, budget_succ hc]
      have hF : ((Fintype.card S : ℝ) - Q) ≤ (t.freeIn.card : ℝ) := by
        rw [hwf.card_freeIn, Nat.cast_sub hwf.length_le]
        have : (t.length : ℝ) ≤ Q := by exact_mod_cast (by omega : t.length ≤ Q)
        linarith
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
          have := budget_nonneg (k := k) (u := u) hQ (c + 1)
          linarith
      · refine (sum_ind_bad_le B k u (fun x => ⟨.inv, x, y⟩) (hIp y) (hIs y) t hgood _).trans ?_
        push_cast
        have : (t.length : ℝ) ≤ c := by exact_mod_cast hlen
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- The explicit value of the whole budget. -/
theorem budget_zero (card k u Q : ℕ) :
    budget card k u Q 0 =
      ((Q : ℝ) * ((Q : ℝ) - 1) / 2 * k + (Q : ℝ) * u) / ((card : ℝ) - Q) := by
  unfold budget
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Nat.Ico_zero_eq_range,
    Finset.card_range, nsmul_eq_mul]
  congr 2
  have h := Finset.sum_range_id_mul_two Q
  have h' : ((∑ i ∈ Finset.range Q, i : ℕ) : ℝ) * 2 = (Q : ℝ) * ((Q : ℝ) - 1) := by
    rcases Q with _ | Q
    · simp
    · have : ((∑ i ∈ Finset.range (Q + 1), i : ℕ) : ℝ) * 2 =
          (((Q + 1) * (Q + 1 - 1) : ℕ) : ℝ) := by exact_mod_cast h
      rw [this]
      push_cast
      ring
  rw [Nat.cast_sum] at h'
  linarith

/-- **Union bound over queries.** For every strategy, the probability that the table is bad at
the end while at most `Q` queries were made is at most
`(Q (Q - 1) / 2 · k + Q · u) / (|S| - Q)`. -/
theorem prob_not_good_le (B : BadSpec S) (k u Q : ℕ) (hQ : Q < Fintype.card S)
    (hFp : ∀ (x : S) (old : Entry S),
      ∃ F : Finset S, F.card ≤ k ∧ ∀ y, B.pair ⟨.fwd, x, y⟩ old → y ∈ F)
    (hFs : ∀ x : S, ∃ F : Finset S, F.card ≤ u ∧ ∀ y, B.single ⟨.fwd, x, y⟩ → y ∈ F)
    (hIp : ∀ (y : S) (old : Entry S),
      ∃ F : Finset S, F.card ≤ k ∧ ∀ x, B.pair ⟨.inv, x, y⟩ old → x ∈ F)
    (hIs : ∀ y : S, ∃ F : Finset S, F.card ≤ u ∧ ∀ x, B.single ⟨.inv, x, y⟩ → x ∈ F)
    (st : Strat S α) :
    st.prob PState.init (fun _ s' => ¬ B.Good s'.trace ∧ s'.count ≤ Q) ≤
      ((Q : ℝ) * ((Q : ℝ) - 1) / 2 * k + (Q : ℝ) * u) / ((Fintype.card S : ℝ) - Q) := by
  rw [← budget_zero]
  exact exp_not_good_le B k u Q hQ hFp hFs hIp hIs st PState.init Trace.WF.nil (le_refl _)
    B.good_nil

end Bound

end CommitGolfCandidate.Permutation
