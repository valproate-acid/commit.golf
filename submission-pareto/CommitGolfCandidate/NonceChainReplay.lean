import CommitGolfCandidate.NonceChainPath
import CommitGolfCandidate.NonceChainHidden
import Mathlib.Data.List.FinRange

/-! A tape can be checked after any public forward/inverse strategy. Multiplying
by the number of possible tapes recovers the real-chain event probability when
the tape is averaged. -/
namespace CommitGolfCandidate.Permutation.NonceChain
open Finset
set_option linter.unusedSectionVars false
variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {n : Nat}

def edges (v : Fin (n+1) → S) : List (S × S) :=
  List.ofFn fun i : Fin n => (v i.castSucc, v i.succ)

def follows (π : Equiv.Perm S) (v : Fin (n+1) → S) : Prop :=
  ∀ i : Fin n, π (v i.castSucc) = v i.succ

theorem fresh_edges (v : Fin (n+1) → S) (t : Trace S)
    (safe : ¬Exposed v (t.usedIn ∪ t.usedOut)) : Fresh (edges v) t := by
  have inj : Function.Injective v := by
    intro i j eq
    by_contra diff
    exact safe ⟨i, Or.inr ⟨j,Ne.symm diff,eq⟩⟩
  apply fresh_of_nodup
  · rw [edges, List.map_ofFn, List.nodup_ofFn]
    exact inj.comp (Fin.castSucc_injective n)
  · rw [edges, List.map_ofFn, List.nodup_ofFn]
    exact inj.comp (Fin.succ_injective n)
  · intro e he hi
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact safe ⟨_, Or.inl (mem_union_left _ hi)⟩
  · intro e he ho
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact safe ⟨_, Or.inl (mem_union_right _ ho)⟩

private theorem eager_bind {A D : Type} (π : Equiv.Perm S) (g : Strat S A)
    (k : A → Strat S D) (s : PState S) (f : D → PState S → ℝ) :
    (g.bind k).eager π s f = g.eager π s (fun a s' => (k a).eager π s' f) := by
  induction g generalizing s with
  | done => rfl
  | fwd x k ih => exact ih _ _
  | inv y k ih => exact ih _ _
  | rand m k ih => exact avg_congr fun i _ => ih i _

private theorem eager_zero {A : Type} (π : Equiv.Perm S) (g : Strat S A) (s : PState S) :
    g.eager π s (fun _ _ => 0) = 0 := by
  induction g generalizing s with
  | done => rfl
  | fwd x k ih => exact ih _ _
  | inv y k ih => exact ih _ _
  | rand m k ih => simp [Strat.eager, ih, avg_zero]

noncomputable def accept (b : Bool) := ind (b = true)

open Classical in
noncomputable def weight (g : Strat S Bool) (v : Fin (n+1) → S) : ℝ :=
  mean fun π : Equiv.Perm S => if follows π v then
    g.eager π PState.init (fun b _ => accept b) else 0

theorem weight_eq (g : Strat S Bool) (v : Fin (n+1) → S) :
    weight g v = g.exp PState.init (fun b st => if b then
      (checkEdges (edges v)).prob st (fun b' _ => b' = true) else 0) := by
  classical
  let k : Bool → Strat S Bool := fun b => if b then checkEdges (edges v) else .done false
  have eager (π : Equiv.Perm S) :
      (g.bind k).eager π PState.init (fun b _ => accept b) =
        if follows π v then g.eager π PState.init (fun b _ => accept b) else 0 := by
    rw [eager_bind]
    have leaf (b : Bool) (st : PState S) :
        (k b).eager π st (fun b _ => accept b) =
        if follows π v then accept b else 0 := by
      cases b
      · simp [k, Strat.eager, accept, ind]
      · simp only [k, if_true, check_eager]
        have eq : (∀ e ∈ edges v, π e.1 = e.2) ↔ follows π v := by
          simp [edges, List.forall_mem_ofFn_iff,follows]
        by_cases good : follows π v
        · rw [decide_eq_true (eq.mpr good), if_pos good]
        · rw [decide_eq_false (fun h => good (eq.mp h)), if_neg good]
          simp [accept,ind]
    simp only [leaf]
    by_cases good : follows π v <;> simp [good,eager_zero]
  rw [weight, mean, avg_congr (fun π _ => (eager π).symm), Strat.avg_eager, Strat.exp_bind]
  apply congrArg (g.exp PState.init)
  funext b st
  cases b <;> simp [k,Strat.prob,accept,Strat.exp,ind]

theorem path_comparison (g : Strat S Bool) (v : Fin (n+1) → S) :
    g.exp PState.init (fun b _ => accept b) ≤
      (Fintype.card S : ℝ)^n * weight g v +
        g.exp PState.init (fun _ st => ind (Exposed v (st.trace.usedIn ∪ st.trace.usedOut))) := by
  classical
  rw [weight_eq, ← Strat.exp_mul_left, ← Strat.exp_add]
  apply Strat.exp_mono
  intro b st
  have pos : 0 < (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos
  have nonneg := (checkEdges (edges v)).prob_nonneg st (fun b' _ => b' = true)
  cases b
  · simp [accept,ind_neg,ind_nonneg]
  · by_cases h : Exposed v (st.trace.usedIn ∪ st.trace.usedOut)
    · simp [accept, ind_pos h, ind_pos True.intro, mul_nonneg (pow_nonneg pos.le _) nonneg]
    · have prob := check_fresh (edges v) st (fresh_edges v st.trace h)
      rw [show (edges v).length = n by simp [edges], one_div_pow] at prob
      have one := (div_le_iff₀ (pow_pos pos n)).mp prob
      simpa [accept, ind_pos True.intro, ind_neg h, mul_comm] using one

end CommitGolfCandidate.Permutation.NonceChain
