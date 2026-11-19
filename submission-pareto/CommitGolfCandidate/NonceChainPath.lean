import CommitGolfCandidate.S3PermEager

/-! Conditioning a uniform permutation on a proposed chain.
A successful replay after the public transcript checks every proposed edge
against the same permutation. On a fresh path each required answer has
conditional probability at least the reciprocal of the state-space size. -/
namespace CommitGolfCandidate.Permutation.NonceChain

open Finset
variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

def checkEdges : List (S × S) → Strat S Bool
  | [] => .done true
  | (x, y) :: rest => .fwd x fun z => if z = y then checkEdges rest else .done false

def Fresh : List (S × S) → Trace S → Prop
  | [], _ => True
  | (x, y) :: rest, t =>
    x ∉ t.usedIn ∧ y ∉ t.usedOut ∧ Fresh rest (⟨.fwd, x, y⟩ :: t)

theorem fresh_of_nodup (es : List (S × S)) (t : Trace S)
    (hx : (es.map Prod.fst).Nodup) (hy : (es.map Prod.snd).Nodup)
    (hi : ∀ e ∈ es, e.1 ∉ t.usedIn) (ho : ∀ e ∈ es, e.2 ∉ t.usedOut) : Fresh es t := by
  induction es generalizing t with
  | nil => trivial
  | cons e es ih =>
    rcases e with ⟨x, y⟩
    simp only [List.map_cons, List.nodup_cons] at hx hy
    refine ⟨hi _ List.mem_cons_self, ho _ List.mem_cons_self, ih _ hx.2 hy.2 ?_ ?_⟩
    · intro e he
      have outside := hi e (List.mem_cons_of_mem _ he)
      have diff : e.1 ≠ x := fun h => hx.1 (h ▸ List.mem_map_of_mem he)
      simpa [Trace.usedIn, diff] using outside
    · intro e he
      have outside := ho e (List.mem_cons_of_mem _ he)
      have diff : e.2 ≠ y := fun h => hy.1 (h ▸ List.mem_map_of_mem he)
      simpa [Trace.usedOut, diff] using outside

private theorem avg_single_term {ι : Type} [Fintype ι]
    (a : Finset ι) (f : ι → ℝ) (i : ι) (inside : i ∈ a)
    (nonneg : ∀ j ∈ a, 0 ≤ f j) :
    f i / Fintype.card ι ≤ avg a f := by
  have pos : 0 < (a.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨i, inside⟩
  unfold avg
  exact le_trans (div_le_div_of_nonneg_left (nonneg i inside) pos (by exact_mod_cast a.card_le_univ))
    (div_le_div_of_nonneg_right (Finset.single_le_sum nonneg inside) pos.le)

/-- Lower likelihood of a disjoint, consistent list of programmed edges after any public run. -/
theorem check_fresh (es : List (S × S)) (s : PState S) (fresh : Fresh es s.trace) :
    (1 / (Fintype.card S : ℝ)) ^ es.length ≤ (checkEdges es).prob s (fun b _ => b = true) := by
  classical
  induction es generalizing s with
  | nil => simp [checkEdges, Strat.prob, Strat.exp, ind]
  | cons e es ih =>
    rcases e with ⟨x,y⟩
    obtain ⟨unusedX, unusedY, rest⟩ := fresh
    have member : y ∈ s.trace.fwdAns x := by
      simpa [Trace.fwdAns, unusedX] using unusedY
    let term := fun z : S =>
      ((if z = y then checkEdges es else Strat.done false) : Strat S Bool).prob
        ⟨s.trace.stepF x z, s.count + 1⟩ (fun b _ => b = true)
    have single := avg_single_term (s.trace.fwdAns x) term y member
      (fun z _ => Strat.prob_nonneg _ _ _)
    have yterm : term y = (checkEdges es).prob
        ⟨⟨.fwd,x,y⟩ :: s.trace, s.count+1⟩ (fun b _ => b = true) := by
      simp [term,Trace.stepF,unusedX]
    rw [List.length_cons, pow_succ, mul_one_div]
    exact le_trans (div_le_div_of_nonneg_right ((ih _ rest).trans_eq yterm.symm)
      (Nat.cast_nonneg _)) single

theorem check_eager (es : List (S × S)) (π : Equiv.Perm S) (s : PState S) (f : Bool → ℝ) :
    (checkEdges es).eager π s (fun b _ => f b) = f (decide (∀ e ∈ es, π e.1 = e.2)) := by
  classical
  induction es generalizing s with
  | nil => simp [checkEdges, Strat.eager]
  | cons e es ih =>
    rcases e with ⟨x,y⟩
    by_cases h : π x = y
    · simpa [checkEdges, Strat.eager, h] using (ih ⟨s.trace.stepF x (π x), s.count+1⟩)
    · simp [checkEdges, Strat.eager, h]

end CommitGolfCandidate.Permutation.NonceChain
