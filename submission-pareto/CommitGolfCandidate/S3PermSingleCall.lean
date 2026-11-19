import CommitGolfCandidate.S3PermBadEvent

/-!
# One permutation call with a fixed prefix and a truncated output

`f(x) = trunc (π (enc x))`, where `enc` is an injective encoding of the input into the state
(for the prepend construction of Dodis, Reyzin, Rivest and Shen, FSE 2009: `enc x = prefix ‖ x`)
and `trunc` keeps part of the output. Following Remark 1 of that paper the statement is for any
injective `enc` and any `trunc`; the sizes enter only through `K`, a bound on the number of
states with a given truncation, and `V`, a bound on the number of valid inputs `enc x`.

The two bad events of the proof are named:

* `OutputCollision`: the answer to a fresh forward query agrees, after truncation, with the
  output of an older table entry;
* `InverseHitsPrefix`: the answer to a fresh inverse query is a valid input `enc x`.

`collision_imp_bad` is the deterministic extraction lemma, `collision_bound` the probability
bound, `collision_bound_level` its reading at a security level.
-/

set_option linter.unusedSectionVars false

namespace CommitGolfCandidate.Permutation

open Finset

variable {S : Type} [Fintype S] [DecidableEq S]

namespace Strat

/-- Reasoning rule for a forward query inside a game: afterwards the table is well formed,
extends the old one, and holds the returned pair. -/
theorem post_fwd {α : Type} {x : S} {k : S → Strat S α} {s : PState S}
    {P : α → PState S → Prop} (hs : s.trace.WF)
    (h : ∀ (y : S) (s' : PState S), s'.trace.WF → s.trace <:+ s'.trace →
      (∃ e ∈ s'.trace, e.inp = x ∧ e.out = y) → s'.count = s.count + 1 → (k y).post s' P) :
    (Strat.fwd x k).post s P :=
  fun y hy => h y _ (hs.stepF hy) (Trace.suffix_stepF _ _ _)
    (Trace.mem_stepF_of_mem_fwdAns hy) rfl

end Strat

/-! ### The numerical bound and its reading at a security level -/

/-- `(Q (Q - 1) / 2 · k + Q · u) / (N - Q)`: the union bound for `Q` queries to a permutation of
`N` states when each fresh answer has at most `k` bad values per older entry and `u` bad values
of its own. -/
noncomputable def unionBound (N k u Q : ℕ) : ℝ :=
  ((Q : ℝ) * ((Q : ℝ) - 1) / 2 * k + (Q : ℝ) * u) / ((N : ℝ) - Q)

/-- Reading at security level `lam`: if `2^lam (2^lam k + 2 u) ≤ 2 (N - 2^lam)` then the union
bound is at most `Q / 2^lam` for every `Q ≤ 2^lam`. -/
theorem unionBound_le_level (N k u Q lam : ℕ) (hQ : Q ≤ 2 ^ lam) (hN : 2 ^ lam < N)
    (hlev : 2 ^ lam * (2 ^ lam * k + 2 * u) ≤ 2 * (N - 2 ^ lam)) :
    unionBound N k u Q ≤ (Q : ℝ) / 2 ^ lam := by
  have hL0 : (0 : ℝ) < (2 : ℝ) ^ lam := by positivity
  have hQL : (Q : ℝ) ≤ (2 : ℝ) ^ lam := by exact_mod_cast hQ
  have hLN : (2 : ℝ) ^ lam < (N : ℝ) := by exact_mod_cast hN
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hlev' : (2 : ℝ) ^ lam * ((2 : ℝ) ^ lam * k + 2 * u) ≤ 2 * ((N : ℝ) - (2 : ℝ) ^ lam) := by
    have h := hlev
    rw [← Nat.cast_le (α := ℝ)] at h
    push_cast [Nat.cast_sub hN.le] at h
    exact h
  have h1 : ((Q : ℝ) - 1) / 2 * k + u ≤ ((2 : ℝ) ^ lam * k + 2 * u) / 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (2 : ℝ) ^ lam - Q + 1) hk0]
  have hden : (0 : ℝ) < (N : ℝ) - Q := by linarith
  unfold unionBound
  rw [div_le_div_iff₀ hden hL0]
  calc ((Q : ℝ) * ((Q : ℝ) - 1) / 2 * k + (Q : ℝ) * u) * (2 : ℝ) ^ lam
      = (Q : ℝ) * ((((Q : ℝ) - 1) / 2 * k + u) * (2 : ℝ) ^ lam) := by ring
    _ ≤ (Q : ℝ) * ((((2 : ℝ) ^ lam * k + 2 * u) / 2) * (2 : ℝ) ^ lam) := by gcongr
    _ = (Q : ℝ) * ((2 : ℝ) ^ lam * ((2 : ℝ) ^ lam * k + 2 * u) / 2) := by ring
    _ ≤ (Q : ℝ) * ((N : ℝ) - (2 : ℝ) ^ lam) := by gcongr; linarith
    _ ≤ (Q : ℝ) * ((N : ℝ) - Q) := by gcongr

/-- A probability that is at most `Q / 2^lam` for `Q ≤ 2^lam` is at most
`min 1 ((Q + 1) / 2^lam)` for every `Q`. -/
theorem le_min_one_of_level {p : ℝ} {Q lam : ℕ} (hp1 : p ≤ 1)
    (hp : Q ≤ 2 ^ lam → p ≤ (Q : ℝ) / 2 ^ lam) : p ≤ min 1 (((Q : ℝ) + 1) / 2 ^ lam) := by
  have hL0 : (0 : ℝ) < (2 : ℝ) ^ lam := by positivity
  refine le_min hp1 ?_
  by_cases hQ : Q ≤ 2 ^ lam
  · refine (hp hQ).trans ?_
    gcongr
    linarith
  · have hQL : (2 : ℝ) ^ lam ≤ (Q : ℝ) := by exact_mod_cast (Nat.le_of_not_le hQ)
    refine hp1.trans ?_
    rw [le_div_iff₀ hL0]
    linarith

/-! ### The construction -/

/-- A single-call hash: an injective input encoding and an output truncation. -/
structure SingleCall (S X D : Type) where
  enc : X → S
  enc_inj : Function.Injective enc
  trunc : S → D

namespace SingleCall

variable {X D : Type} (H : SingleCall S X D)

/-- The bad events of the single-call proof. -/
def badSpec : BadSpec S where
  pair new old := new.dir = .fwd ∧ H.trunc new.out = H.trunc old.out
  single e := e.dir = .inv ∧ ∃ x, H.enc x = e.inp

/-- Bad event 1: the answer to a fresh forward query has the same truncation as the output of an
older entry of the table. -/
def OutputCollision (t : Trace S) : Prop :=
  ¬ t.Pairwise fun new old => ¬ H.badSpec.pair new old

/-- Bad event 2: the answer to a fresh inverse query is a valid input (it carries the fixed
prefix). -/
def InverseHitsPrefix (t : Trace S) : Prop :=
  ∃ e ∈ t, e.dir = .inv ∧ ∃ x, H.enc x = e.inp

theorem not_good_iff (t : Trace S) :
    ¬ H.badSpec.Good t ↔ H.OutputCollision t ∨ H.InverseHitsPrefix t := by
  constructor
  · intro h
    by_contra hc
    rw [not_or] at hc
    exact h ⟨not_not.1 hc.1, fun e he hs => hc.2 ⟨e, he, hs⟩⟩
  · rintro (h | ⟨e, he, hs⟩) hg
    · exact h hg.1
    · exact hg.2 e he hs

/-- The table determines the hash of `x`, and its value is `d`. -/
def Evaluates (t : Trace S) (x : X) (d : D) : Prop :=
  ∃ e ∈ t, e.inp = H.enc x ∧ H.trunc e.out = d

/-- **Extraction (deterministic).** If the table holds the calls for two different inputs with
the same hash value, one of the two bad events is in the table. -/
theorem collision_imp_bad {t : Trace S} {x x' : X} {d : D} (hne : x ≠ x')
    (h : H.Evaluates t x d) (h' : H.Evaluates t x' d) :
    H.OutputCollision t ∨ H.InverseHitsPrefix t := by
  rw [← not_good_iff]
  intro hg
  obtain ⟨e, he, hx, hd⟩ := h
  obtain ⟨e', he', hx', hd'⟩ := h'
  have hee : e ≠ e' := by
    rintro rfl
    exact hne (H.enc_inj (hx.symm.trans hx'))
  have key : ∀ a b : Entry S, a ∈ t → (∃ x, H.enc x = a.inp) →
      H.trunc a.out = H.trunc b.out → ¬ H.badSpec.pair a b → False := by
    intro a b ha hax hab hnp
    cases hdir : a.dir with
    | fwd => exact hnp ⟨hdir, hab⟩
    | inv => exact hg.not_single ha ⟨hdir, hax⟩
  rcases hg.not_pair he he' hee with h1 | h1
  · exact key e e' he ⟨x, hx.symm⟩ (hd.trans hd'.symm) h1
  · exact key e' e he' ⟨x', hx'.symm⟩ (hd'.trans hd.symm) h1

/-- Evaluate the hash with one forward query. -/
def eval (x : X) : Strat S D := .fwd (H.enc x) fun y => .done (H.trunc y)

/-- The collision game: the adversary outputs two inputs, then the game evaluates the hash on
both. The two evaluation queries are counted like the adversary's own. -/
def collisionGame (A : Strat S (X × X)) : Strat S ((X × X) × (D × D)) :=
  A.bind fun p => (H.eval p.1).bind fun d => (H.eval p.2).bind fun d' => .done (p, (d, d'))

/-- The adversary wins with two different inputs of equal hash. -/
def Wins (r : (X × X) × (D × D)) : Prop := r.1.1 ≠ r.1.2 ∧ r.2.1 = r.2.2

theorem collisionGame_post (A : Strat S (X × X)) :
    (H.collisionGame A).post PState.init fun r s' =>
      H.Evaluates s'.trace r.1.1 r.2.1 ∧ H.Evaluates s'.trace r.1.2 r.2.2 := by
  unfold collisionGame
  refine Strat.post_bind (Strat.post_mono ?_ (Strat.post_inv A PState.init Trace.WF.nil))
  rintro ⟨x, x'⟩ s1 ⟨hwf1, -, -⟩
  show (Strat.fwd (H.enc x) _).post s1 _
  refine Strat.post_fwd hwf1 fun y s2 hwf2 _ hmem2 _ => ?_
  show (Strat.fwd (H.enc x') _).post s2 _
  refine Strat.post_fwd hwf2 fun y' s3 hwf3 hsuf3 hmem3 _ => ?_
  obtain ⟨e, he, h1, h2⟩ := hmem2
  obtain ⟨e', he', h1', h2'⟩ := hmem3
  exact ⟨⟨e, hsuf3.subset he, h1, by rw [h2]⟩, ⟨e', he', h1', by rw [h2']⟩⟩

/-- **Single-call collision bound.** Let at most `K` states share any truncation and let there
be at most `V` valid inputs. For every adversary, the probability that it outputs two different
inputs with the same hash while the whole experiment makes at most `Q` forward or inverse
queries is at most `(Q (Q - 1) / 2 · K + Q · V) / (|S| - Q)`: a birthday term for
`OutputCollision` plus a term linear in `Q` for `InverseHitsPrefix`. -/
theorem collision_bound [Fintype X] [DecidableEq D] (K V Q : ℕ) (hQ : Q < Fintype.card S)
    (hK : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ K)
    (hV : Fintype.card X ≤ V) (A : Strat S (X × X)) :
    (H.collisionGame A).prob PState.init (fun r s' => Wins r ∧ s'.count ≤ Q) ≤
      unionBound (Fintype.card S) K V Q := by
  refine (Strat.prob_le_prob_of_post (H.collisionGame_post A) ?_).trans
    (prob_not_good_le H.badSpec K V Q hQ ?_ ?_ ?_ ?_ _)
  · rintro r s' ⟨h1, h2⟩ ⟨⟨hne, heq⟩, hc⟩
    refine ⟨(H.not_good_iff _).2 (H.collision_imp_bad hne h1 ?_), hc⟩
    rw [heq]
    exact h2
  · intro x old
    exact ⟨univ.filter fun s => H.trunc s = H.trunc old.out, hK _,
      fun y hy => Finset.mem_filter.2 ⟨Finset.mem_univ _, hy.2⟩⟩
  · intro x
    exact ⟨∅, Nat.zero_le _, fun y hy => by simp [badSpec] at hy⟩
  · intro y old
    exact ⟨∅, Nat.zero_le _, fun x hx => by simp [badSpec] at hx⟩
  · intro y
    refine ⟨univ.image H.enc, Finset.card_image_le.trans (by simpa using hV), fun x hx => ?_⟩
    obtain ⟨x0, h0⟩ := hx.2
    exact Finset.mem_image.2 ⟨x0, Finset.mem_univ _, h0⟩

theorem eval_QB (x : X) : (H.eval x).QB 1 := .fwd _ _ 0 fun _ => .done _ 0

theorem collisionGame_QB {A : Strat S (X × X)} {q : ℕ} (hA : A.QB q) :
    (H.collisionGame A).QB (q + 2) := by
  unfold collisionGame
  refine Strat.QB.bind hA fun p => ?_
  exact (Strat.QB.bind (H.eval_QB p.1) fun d =>
    (Strat.QB.bind (H.eval_QB p.2) fun d' => Strat.QB.done _ 0)).mono (by omega)

/-- The same bound for an adversary limited to `q` queries: with the two evaluation queries the
experiment makes at most `q + 2`. -/
theorem collision_bound_of_QB [Fintype X] [DecidableEq D] (K V q : ℕ)
    (hq : q + 2 < Fintype.card S)
    (hK : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ K)
    (hV : Fintype.card X ≤ V) (A : Strat S (X × X)) (hA : A.QB q) :
    (H.collisionGame A).prob PState.init (fun r _ => Wins r) ≤
      unionBound (Fintype.card S) K V (q + 2) := by
  refine (Strat.prob_le_prob_of_post (Strat.post_QB (H.collisionGame_QB hA) PState.init) ?_).trans
    (H.collision_bound K V (q + 2) hq hK hV A)
  rintro r s' ⟨-, hc⟩ hw
  exact ⟨hw, by simpa [PState.init] using hc⟩

/-- Reading at a security level: under the arithmetic condition on the sizes, the collision
probability with at most `Q` queries is at most `min 1 ((Q + 1) / 2^lam)` for every `Q`. -/
theorem collision_bound_level [Fintype X] [DecidableEq D] (K V lam : ℕ)
    (hN : 2 ^ lam < Fintype.card S)
    (hK : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ K)
    (hV : Fintype.card X ≤ V)
    (hlev : 2 ^ lam * (2 ^ lam * K + 2 * V) ≤ 2 * (Fintype.card S - 2 ^ lam))
    (A : Strat S (X × X)) (Q : ℕ) :
    (H.collisionGame A).prob PState.init (fun r s' => Wins r ∧ s'.count ≤ Q) ≤
      min 1 (((Q : ℝ) + 1) / 2 ^ lam) := by
  refine le_min_one_of_level (Strat.prob_le_one _ _ _) fun hQ => ?_
  exact (H.collision_bound K V Q (lt_of_le_of_lt hQ hN) hK hV A).trans
    (unionBound_le_level _ K V Q lam hQ hN hlev)

set_option exponentiation.threshold 2000 in
/-- The sizes of a 1,600-bit permutation with a 128-bit fixed prefix and a 256-bit output give
120-bit collision resistance: this is the arithmetic condition of `collision_bound_level` for
`|S| = 2^1600`, `K = 2^1344`, `V = 2^1472`, `lam = 120`. -/
theorem level_1600_128_256 :
    2 ^ 120 * (2 ^ 120 * 2 ^ 1344 + 2 * 2 ^ 1472) ≤ 2 * (2 ^ 1600 - 2 ^ 120) := by
  norm_num

end SingleCall

end CommitGolfCandidate.Permutation
