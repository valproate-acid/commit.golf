import CommitGolfCandidate.NonceChainReplay

/-! Replacement of a permutation chain by a uniformly sampled public tape. The
strategy receives every emitted prefix and can make arbitrary adaptive queries,
in either direction. Its budget includes the honest computation on the tape. -/
namespace CommitGolfCandidate.Permutation.NonceChain
open Finset
set_option linter.unusedSectionVars false
variable {S K D : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype K] [Nonempty K] [Fintype D] [Nonempty D] {n : Nat}

def orbit (π : Equiv.Perm S) (x : S) : Nat → S
  | 0 => x
  | j + 1 => π (orbit π x j)

def vertices (start : K → S) (k : K) (z : Fin n → S) : Fin (n+1) → S :=
  Fin.cases (start k) z

theorem follows_iff (π : Equiv.Perm S) (start : K → S) (k : K) (z : Fin n → S) :
    follows π (vertices start k z) ↔ z = fun i => orbit π (start k) (i.val+1) := by
  constructor
  · intro h
    have all (j : Fin (n+1)) : vertices start k z j = orbit π (start k) j.val := by
      induction j using Fin.induction with
      | zero => rfl
      | succ i ih => exact (h i).symm.trans (congrArg π ih)
    funext i
    exact all i.succ
  · rintro rfl i
    have one (j : Fin (n+1)) :
        vertices start k (fun i : Fin n => orbit π (start k) (i.val+1)) j =
          orbit π (start k) j.val := Fin.cases rfl (fun _ => rfl) j
    rw [one,one]
    rfl

def partition (split : S ≃ D × K) (n : Nat) :
    ((Fin n → D) × (Fin (n+1) → K)) ≃ K × (Fin n → S) where
  toFun a := ⟨a.2 0, fun i => split.symm (a.1 i,a.2 i.succ)⟩
  invFun a := ⟨fun i => (split (a.2 i)).1, Fin.cases a.1 (fun i => (split (a.2 i)).2)⟩
  left_inv a := by
    apply Prod.ext
    · funext i
      simp
    · funext j
      exact Fin.cases rfl (fun i => by simp) j
  right_inv a := by
    apply Prod.ext
    · rfl
    · funext i
      simp

def encodeAt (split : S ≃ D × K) (start : K → S) (p : Fin n → D) :
    Fin (n+1) → K → S := Fin.cases start (fun i h => split.symm (p i,h))

theorem encodeAt_injective (split : S ≃ D × K) (start : K → S)
    (hs : Function.Injective start) (p : Fin n → D) (i : Fin (n+1)) :
    Function.Injective (encodeAt split start p i) := by
  refine Fin.cases hs (fun j a b eq => ?_) i
  exact congrArg Prod.snd (split.symm.injective eq)

theorem partition_vertices (split : S ≃ D × K) (start : K → S) (p : Fin n → D)
    (h : Fin (n+1) → K) :
    vertices start ((partition split n) (p,h)).1 ((partition split n) (p,h)).2 =
      fun i => encodeAt split start p i (h i) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem mean_swap {A B : Type} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    mean (fun a => mean (f a)) = mean (fun b => mean (fun a => f a b)) := by
  rw [← mean_prod, ← mean_prod]
  exact mean_equiv (Equiv.prodComm A B) (fun p : B × A => f p.2 p.1)

private theorem exp_mean {A : Type} [Fintype A] {T : Type}
    (g : Strat S T) (s : PState S) (f : A → T → PState S → ℝ) :
    mean (fun a => g.exp s (f a)) = g.exp s (fun b st => mean (fun a => f a b st)) := by
  unfold mean avg
  simp_rw [div_eq_inv_mul, ← Strat.exp_sum, ← Strat.exp_mul_left]

private theorem bad_expectation (g : Strat S Bool) {q : Nat} (bounded : g.QB q)
    (encode : Fin (n+1) → K → S) (inj : ∀ i, Function.Injective (encode i)) :
    mean (fun h : Fin (n+1) → K => g.exp PState.init (fun _ st =>
      ind (Exposed (fun i => encode i (h i)) (st.trace.usedIn ∪ st.trace.usedOut)))) ≤
      ((n+1 : Nat) : ℝ) * ((2*q+(n+1) : ℝ) / Fintype.card K) := by
  rw [exp_mean]
  have post := Strat.post_and (g.post_inv PState.init Trace.WF.nil) (Strat.post_QB bounded PState.init)
  rw [← g.exp_const (((n+1 : Nat) : ℝ) * ((2*q+(n+1) : ℝ) / Fintype.card K))
    PState.init Trace.WF.nil]
  apply Strat.exp_le_exp_of_post post
  intro b st h
  have len : st.trace.length ≤ q := by simpa [PState.init] using h.2.1
  have size : (st.trace.usedIn ∪ st.trace.usedOut).card ≤ 2*q := by
    have c := Finset.card_union_le st.trace.usedIn st.trace.usedOut
    rw [h.1.1.card_usedIn,h.1.1.card_usedOut] at c
    omega
  have delta := exposed_bound encode inj (st.trace.usedIn ∪ st.trace.usedOut)
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] at delta ⊢
  refine delta.trans ?_
  gcongr
  exact_mod_cast size

noncomputable def realProb (split : S ≃ D × K) (start : K → S)
    (g : (Fin n → D) → Strat S Bool) : ℝ :=
  mean fun π : Equiv.Perm S => mean fun k : K =>
    (g (fun i => (split (orbit π (start k) (i.val+1))).1)).eager π PState.init
      (fun b _ => accept b)

noncomputable def idealProb (g : (Fin n → D) → Strat S Bool) : ℝ :=
  mean fun p => (g p).exp PState.init (fun b _ => accept b)

/-- Averaging the replay over all proposed paths counts each actual orbit exactly once. -/
theorem sum_weight (split : S ≃ D × K) (start : K → S) (g : (Fin n → D) → Strat S Bool) :
    (Fintype.card S : ℝ)^n * mean (fun p : Fin n → D => mean (fun h : Fin (n+1) → K =>
      weight (g p) (fun i => encodeAt split start p i (h i)))) = realProb split start g := by
  classical
  let F := fun (k : K) (z : Fin n → S) =>
    weight (g (fun i => (split (z i)).1)) (vertices start k z)
  have reorder : mean (fun p : Fin n → D => mean (fun h : Fin (n+1) → K =>
        weight (g p) (fun i => encodeAt split start p i (h i)))) =
        mean (fun k => mean (F k)) := by
    rw [← mean_prod, ← mean_prod, ← mean_equiv (partition split n) (fun a => F a.1 a.2)]
    apply avg_congr
    rintro ⟨p,h⟩ _
    unfold F
    rw [partition_vertices]
    simp [partition]
  rw [reorder]
  unfold F weight
  simp_rw [follows_iff]
  rw [← avg_mul_left]
  apply Eq.trans _ (mean_swap _)
  apply avg_congr
  intro k _
  rw [mean_swap, ← avg_mul_left]
  apply avg_congr
  intro π _
  unfold mean avg
  simp only [Finset.card_univ,Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [Finset.sum_ite_eq' univ]
  simp [field]

/-- One-sided event discrepancy. Running the strategy with the complementary
event bounds the other direction with the same error. -/
theorem ideal_le_real (split : S ≃ D × K) (start : K → S) (inj : Function.Injective start)
    (g : (Fin n → D) → Strat S Bool) (q : Nat) (hq : ∀ p, (g p).QB q) :
    idealProb g ≤ realProb split start g +
      ((n+1 : Nat) : ℝ) * ((2*q+(n+1) : ℝ) / Fintype.card K) := by
  rw [← sum_weight]
  let err := ((n+1 : Nat) : ℝ) * ((2*q+(n+1) : ℝ) / Fintype.card K)
  change mean _ ≤ _ + err
  rw [← avg_mul_left, ← avg_const (Finset.univ_nonempty (α := Fin n → D)) err, ← avg_add]
  apply avg_mono
  intro p _
  let f := encodeAt split start p
  have step (h : Fin (n+1) → K) := path_comparison (g p) (fun i => f i (h i))
  have avgStep := avg_mono (A := univ) (fun h _ => step h)
  rw [avg_const Finset.univ_nonempty, avg_add, avg_mul_left] at avgStep
  exact avgStep.trans (add_le_add_right (bad_expectation (g p) (hq p) f
    (encodeAt_injective split start inj p)) _)

end CommitGolfCandidate.Permutation.NonceChain
