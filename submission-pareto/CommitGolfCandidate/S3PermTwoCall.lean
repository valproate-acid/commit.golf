import CommitGolfCandidate.S3PermSingleCall

/-!
# The two-call leaf hash: collision resistance

The leaf hash of DESIGN.md section 4.1, with every size a parameter:

    o1 = π (enc1 x1)                      first call; `enc1` is injective and its range is the
                                          set of valid first-call inputs (fixed prefix)
    o2 = π (enc2 (r, chop o1, m2))        second call; `chop o1` is the chaining value
    digest = trunc o2

For the design `enc1 (t, m₁) = 0^16 ‖ t ‖ m₁`, `chop` keeps bytes 96..200, `enc2 (r, c, m₂) =
r ‖ c ‖ m₂` and `trunc` keeps bytes 0..32. Nothing below depends on these choices.

Five bad events, named after the role of the fresh answer that causes them:

* `DigestCollision`: a fresh forward answer agrees with an older output on the digest part;
* `ChainCollision`: a fresh forward answer agrees with an older output on the chaining part;
* `InverseHitsPrefix`: a fresh inverse answer is a valid first-call input;
* `InverseHitsChain`: a fresh inverse answer is a second-call input whose chaining slot equals
  the chaining part of an older output;
* `ForwardHitsSlot`: a fresh forward answer has a chaining part equal to the chaining slot of an
  older input.

`collision_imp_bad` is the deterministic extraction lemma: a table that evaluates two different
leaf inputs to the same digest contains one of the five events. `collision_bound` is the
probability bound and `collision_bound_level`, `binding_1600` its reading at 120 bits.
-/

set_option linter.unusedSectionVars false

namespace CommitGolfCandidate.Permutation

open Finset

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The two-call leaf hash. `X1` is the input of the first call (tag and first message part),
`R` the salt, `C` the chaining value, `M2` the second message part, `D` the digest. -/
structure TwoCall (S X1 R C M2 D : Type) where
  enc1 : X1 → S
  enc1_inj : Function.Injective enc1
  chop : S → C
  enc2 : R × C × M2 → S
  enc2_inj : Function.Injective enc2
  trunc : S → D

namespace TwoCall

variable {X1 R C M2 D : Type} (H : TwoCall S X1 R C M2 D)

/-- The bad events of the two-call proof, see the file header. -/
def badSpec : BadSpec S where
  pair new old :=
    (new.dir = .fwd ∧ H.trunc new.out = H.trunc old.out) ∨
    (new.dir = .fwd ∧ H.chop new.out = H.chop old.out) ∨
    (new.dir = .inv ∧ ∃ r m, new.inp = H.enc2 (r, H.chop old.out, m)) ∨
    (new.dir = .fwd ∧ ∃ r m, old.inp = H.enc2 (r, H.chop new.out, m))
  single e := e.dir = .inv ∧ ∃ x, H.enc1 x = e.inp

/-- A fresh forward answer agrees with an older output on the digest part. -/
def DigestCollision (t : Trace S) : Prop :=
  ¬ t.Pairwise fun new old => ¬ (new.dir = .fwd ∧ H.trunc new.out = H.trunc old.out)

/-- A fresh forward answer agrees with an older output on the chaining part. -/
def ChainCollision (t : Trace S) : Prop :=
  ¬ t.Pairwise fun new old => ¬ (new.dir = .fwd ∧ H.chop new.out = H.chop old.out)

/-- A fresh inverse answer is a valid first-call input. -/
def InverseHitsPrefix (t : Trace S) : Prop :=
  ∃ e ∈ t, e.dir = .inv ∧ ∃ x, H.enc1 x = e.inp

/-- A fresh inverse answer is a second-call input whose chaining slot equals the chaining part of
an older output. -/
def InverseHitsChain (t : Trace S) : Prop :=
  ¬ t.Pairwise fun new old =>
    ¬ (new.dir = .inv ∧ ∃ r m, new.inp = H.enc2 (r, H.chop old.out, m))

/-- A fresh forward answer has a chaining part equal to the chaining slot of an older input. -/
def ForwardHitsSlot (t : Trace S) : Prop :=
  ¬ t.Pairwise fun new old =>
    ¬ (new.dir = .fwd ∧ ∃ r m, old.inp = H.enc2 (r, H.chop new.out, m))

/-- One of the five named bad events is in the table. -/
def Bad (t : Trace S) : Prop :=
  H.DigestCollision t ∨ H.ChainCollision t ∨ H.InverseHitsPrefix t ∨ H.InverseHitsChain t ∨
    H.ForwardHitsSlot t

theorem not_good_iff (t : Trace S) : ¬ H.badSpec.Good t ↔ H.Bad t := by
  constructor
  · intro h
    by_contra hc
    unfold Bad at hc
    simp only [not_or] at hc
    obtain ⟨h1, h2, h3, h4, h5⟩ := hc
    refine h ⟨?_, fun e he hs => h3 ⟨e, he, hs⟩⟩
    have h1' := not_not.1 h1
    have h2' := not_not.1 h2
    have h4' := not_not.1 h4
    have h5' := not_not.1 h5
    refine (((h1'.and h2').and h4').and h5').imp ?_
    rintro a b ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ (h | h | h | h)
    · exact ha h
    · exact hb h
    · exact hc h
    · exact hd h
  · intro hb hg
    rcases hb with h | h | ⟨e, he, hs⟩ | h | h
    · exact h (hg.1.imp fun hn hp => hn (Or.inl hp))
    · exact h (hg.1.imp fun hn hp => hn (Or.inr (Or.inl hp)))
    · exact hg.2 e he hs
    · exact h (hg.1.imp fun hn hp => hn (Or.inr (Or.inr (Or.inl hp))))
    · exact h (hg.1.imp fun hn hp => hn (Or.inr (Or.inr (Or.inr hp))))

/-- The table holds both calls of the leaf hash on input `i = (x1, r, m2)`, and the digest is
`d`. -/
def Evaluates (t : Trace S) (i : X1 × R × M2) (d : D) : Prop :=
  ∃ e1 ∈ t, ∃ e2 ∈ t, e1.inp = H.enc1 i.1 ∧
    e2.inp = H.enc2 (i.2.1, H.chop e1.out, i.2.2) ∧ H.trunc e2.out = d

theorem Evaluates.mono {t t' : Trace S} {i : X1 × R × M2} {d : D} (h : t <:+ t')
    (he : H.Evaluates t i d) : H.Evaluates t' i d := by
  obtain ⟨e1, he1, e2, he2, h1, h2, h3⟩ := he
  exact ⟨e1, h.subset he1, e2, h.subset he2, h1, h2, h3⟩

/-- **Extraction (deterministic).** If a table holds the four calls of two different leaf inputs
with the same digest, it contains one of the five bad events. No probability and no
well-formedness of the table is needed. -/
theorem collision_imp_bad {t : Trace S} {i i' : X1 × R × M2} {d : D} (hne : i ≠ i')
    (h : H.Evaluates t i d) (h' : H.Evaluates t i' d) : H.Bad t := by
  rw [← not_good_iff]
  intro hg
  obtain ⟨e1, he1, e2, he2, hx1, hx2, hd⟩ := h
  obtain ⟨e1', he1', e2', he2', hx1', hx2', hd'⟩ := h'
  -- a second-call entry `a2` whose digest part equals that of another entry `b2`, in the case
  -- where `a2` is the newer of the two
  have keyA : ∀ (a1 a2 b2 : Entry S) (j : X1 × R × M2), a1 ∈ t → a2 ∈ t →
      a1.inp = H.enc1 j.1 → a2.inp = H.enc2 (j.2.1, H.chop a1.out, j.2.2) →
      H.trunc a2.out = H.trunc b2.out → ¬ H.badSpec.pair a2 b2 → False := by
    intro a1 a2 b2 j ha1 ha2 hj1 hj2 htr hnp
    cases hdir : a2.dir with
    | fwd => exact hnp (Or.inl ⟨hdir, htr⟩)
    | inv =>
      by_cases heq : a1 = a2
      · subst heq
        exact hg.not_single ha1 ⟨hdir, j.1, hj1.symm⟩
      · rcases hg.not_pair ha2 ha1 (Ne.symm heq) with h | h
        · exact h (Or.inr (Or.inr (Or.inl ⟨hdir, j.2.1, j.2.2, hj2⟩)))
        · cases hdir1 : a1.dir with
          | fwd => exact h (Or.inr (Or.inr (Or.inr ⟨hdir1, j.2.1, j.2.2, hj2⟩)))
          | inv => exact hg.not_single ha1 ⟨hdir1, j.1, hj1.symm⟩
  -- a first-call entry `a1` whose chaining part equals that of another entry `b1`, in the case
  -- where `a1` is the newer of the two
  have keyB : ∀ (a1 b1 : Entry S) (x : X1), a1 ∈ t → a1.inp = H.enc1 x →
      H.chop a1.out = H.chop b1.out → ¬ H.badSpec.pair a1 b1 → False := by
    intro a1 b1 x ha1 hx hch hnp
    cases hdir : a1.dir with
    | fwd => exact hnp (Or.inr (Or.inl ⟨hdir, hch⟩))
    | inv => exact hg.not_single ha1 ⟨hdir, x, hx.symm⟩
  by_cases h2 : e2 = e2'
  · have hinp : H.enc2 (i.2.1, H.chop e1.out, i.2.2) =
        H.enc2 (i'.2.1, H.chop e1'.out, i'.2.2) := by rw [← hx2, ← hx2', h2]
    have hinj := H.enc2_inj hinp
    simp only [Prod.mk.injEq] at hinj
    obtain ⟨hr, hc, hm⟩ := hinj
    have hx : i.1 ≠ i'.1 := fun hx => hne (Prod.ext hx (Prod.ext hr hm))
    have he : e1 ≠ e1' := by
      rintro rfl
      exact hx (H.enc1_inj (hx1.symm.trans hx1'))
    rcases hg.not_pair he1 he1' he with h | h
    · exact keyB e1 e1' i.1 he1 hx1 hc h
    · exact keyB e1' e1 i'.1 he1' hx1' hc.symm h
  · rcases hg.not_pair he2 he2' h2 with h | h
    · exact keyA e1 e2 e2' i he1 he2 hx1 hx2 (hd.trans hd'.symm) h
    · exact keyA e1' e2' e2 i' he1' he2' hx1' hx2' (hd'.trans hd.symm) h

/-! ### The game -/

/-- Evaluate the leaf hash with two forward queries. -/
def eval (i : X1 × R × M2) : Strat S D :=
  .fwd (H.enc1 i.1) fun o1 => .fwd (H.enc2 (i.2.1, H.chop o1, i.2.2)) fun o2 =>
    .done (H.trunc o2)

theorem eval_post (i : X1 × R × M2) (s : PState S) (hs : s.trace.WF) :
    (H.eval i).post s fun d s' =>
      s'.trace.WF ∧ s.trace <:+ s'.trace ∧ H.Evaluates s'.trace i d := by
  show (Strat.fwd (H.enc1 i.1) _).post s _
  refine Strat.post_fwd hs fun o1 s1 hwf1 hsuf1 hm1 _ => ?_
  show (Strat.fwd (H.enc2 (i.2.1, H.chop o1, i.2.2)) _).post s1 _
  refine Strat.post_fwd hwf1 fun o2 s2 hwf2 hsuf2 hm2 _ => ?_
  obtain ⟨e1, he1, h11, h12⟩ := hm1
  obtain ⟨e2, he2, h21, h22⟩ := hm2
  exact ⟨hwf2, hsuf1.trans hsuf2, e1, hsuf2.subset he1, e2, he2, h11, by rw [h12]; exact h21,
    by rw [h22]⟩

theorem eval_QB (i : X1 × R × M2) : (H.eval i).QB 2 :=
  .fwd _ _ 1 fun _ => .fwd _ _ 0 fun _ => .done _ 0

/-- The collision game for the leaf hash: the adversary outputs two leaf inputs, then the game
evaluates the hash on both. The four evaluation queries are counted like the adversary's own. -/
def collisionGame (A : Strat S ((X1 × R × M2) × (X1 × R × M2))) :
    Strat S (((X1 × R × M2) × (X1 × R × M2)) × (D × D)) :=
  A.bind fun p => (H.eval p.1).bind fun d => (H.eval p.2).bind fun d' => .done (p, (d, d'))

/-- The adversary wins with two different leaf inputs of equal digest. In the commitment a
second opening of a position gives such a pair with the same tag inside `x1`. -/
def Wins (r : ((X1 × R × M2) × (X1 × R × M2)) × (D × D)) : Prop :=
  r.1.1 ≠ r.1.2 ∧ r.2.1 = r.2.2

theorem collisionGame_post (A : Strat S ((X1 × R × M2) × (X1 × R × M2))) :
    (H.collisionGame A).post PState.init fun r s' =>
      H.Evaluates s'.trace r.1.1 r.2.1 ∧ H.Evaluates s'.trace r.1.2 r.2.2 := by
  unfold collisionGame
  refine Strat.post_bind (Strat.post_mono ?_ (Strat.post_inv A PState.init Trace.WF.nil))
  rintro ⟨i, i'⟩ s1 ⟨hwf1, -, -⟩
  refine Strat.post_bind (Strat.post_mono ?_ (H.eval_post i s1 hwf1))
  rintro d s2 ⟨hwf2, -, hev⟩
  refine Strat.post_bind (Strat.post_mono ?_ (H.eval_post i' s2 hwf2))
  rintro d' s3 ⟨-, hsuf3, hev'⟩
  exact ⟨Evaluates.mono H hsuf3 hev, hev'⟩

theorem collisionGame_QB {A : Strat S ((X1 × R × M2) × (X1 × R × M2))} {q : ℕ}
    (hA : A.QB q) : (H.collisionGame A).QB (q + 4) := by
  unfold collisionGame
  refine Strat.QB.bind hA fun p => ?_
  exact (Strat.QB.bind (H.eval_QB p.1) fun d =>
    (Strat.QB.bind (H.eval_QB p.2) fun d' => Strat.QB.done _ 0)).mono (by omega)

/-- The probability of the five bad events, for any strategy. `Kd` and `Kc` bound the number of
states with a given digest part and a given chaining part, `K2` bounds the number of second-call
inputs with a given chaining slot, `V` the number of valid first-call inputs. -/
theorem prob_bad_le [Fintype X1] [Fintype R] [Fintype M2] [DecidableEq C] [DecidableEq D]
    {α : Type} (Kd Kc K2 V Q : ℕ) (hQ : Q < Fintype.card S)
    (hKd : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ Kd)
    (hKc : ∀ c : C, (univ.filter fun s => H.chop s = c).card ≤ Kc)
    (hK2 : Fintype.card R * Fintype.card M2 ≤ K2)
    (hV : Fintype.card X1 ≤ V) (st : Strat S α) :
    st.prob PState.init (fun _ s' => H.Bad s'.trace ∧ s'.count ≤ Q) ≤
      unionBound (Fintype.card S) (Kd + 2 * Kc + K2) V Q := by
  classical
  have hmono : st.prob PState.init (fun _ s' => H.Bad s'.trace ∧ s'.count ≤ Q) ≤
      st.prob PState.init (fun _ s' => ¬ H.badSpec.Good s'.trace ∧ s'.count ≤ Q) :=
    Strat.exp_mono (fun _ s' => ind_mono fun h => ⟨(H.not_good_iff _).2 h.1, h.2⟩) st _
  refine hmono.trans (prob_not_good_le H.badSpec (Kd + 2 * Kc + K2) V Q hQ ?_ ?_ ?_ ?_ st)
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
  · intro x
    exact ⟨∅, Nat.zero_le _, fun y hy => by simp [badSpec] at hy⟩
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

/-- **Collision resistance of the two-call leaf hash.** For every adversary, the probability that
it outputs two different leaf inputs with the same digest while the whole experiment makes at
most `Q` forward or inverse queries is at most

  `(Q (Q - 1) / 2 · (Kd + 2 Kc + K2) + Q · V) / (|S| - Q)`. -/
theorem collision_bound [Fintype X1] [Fintype R] [Fintype M2] [DecidableEq C] [DecidableEq D]
    (Kd Kc K2 V Q : ℕ) (hQ : Q < Fintype.card S)
    (hKd : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ Kd)
    (hKc : ∀ c : C, (univ.filter fun s => H.chop s = c).card ≤ Kc)
    (hK2 : Fintype.card R * Fintype.card M2 ≤ K2)
    (hV : Fintype.card X1 ≤ V) (A : Strat S ((X1 × R × M2) × (X1 × R × M2))) :
    (H.collisionGame A).prob PState.init (fun r s' => Wins r ∧ s'.count ≤ Q) ≤
      unionBound (Fintype.card S) (Kd + 2 * Kc + K2) V Q := by
  refine (Strat.prob_le_prob_of_post (H.collisionGame_post A) ?_).trans
    (H.prob_bad_le Kd Kc K2 V Q hQ hKd hKc hK2 hV _)
  rintro r s' ⟨h1, h2⟩ ⟨⟨hne, heq⟩, hc⟩
  refine ⟨H.collision_imp_bad hne h1 ?_, hc⟩
  rw [heq]
  exact h2

/-- The same bound for an adversary limited to `q` queries: with the four evaluation queries the
experiment makes at most `q + 4`. -/
theorem collision_bound_of_QB [Fintype X1] [Fintype R] [Fintype M2] [DecidableEq C]
    [DecidableEq D] (Kd Kc K2 V q : ℕ) (hq : q + 4 < Fintype.card S)
    (hKd : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ Kd)
    (hKc : ∀ c : C, (univ.filter fun s => H.chop s = c).card ≤ Kc)
    (hK2 : Fintype.card R * Fintype.card M2 ≤ K2)
    (hV : Fintype.card X1 ≤ V) (A : Strat S ((X1 × R × M2) × (X1 × R × M2)))
    (hA : A.QB q) :
    (H.collisionGame A).prob PState.init (fun r _ => Wins r) ≤
      unionBound (Fintype.card S) (Kd + 2 * Kc + K2) V (q + 4) := by
  refine (Strat.prob_le_prob_of_post (Strat.post_QB (H.collisionGame_QB hA) PState.init) ?_).trans
    (H.collision_bound Kd Kc K2 V (q + 4) hq hKd hKc hK2 hV A)
  rintro r s' ⟨-, hc⟩ hw
  exact ⟨hw, by simpa [PState.init] using hc⟩

/-- Reading at a security level `lam`: under the arithmetic condition on the sizes, the collision
probability with at most `Q` queries is at most `min 1 ((Q + 1) / 2^lam)`, for every `Q`. -/
theorem collision_bound_level [Fintype X1] [Fintype R] [Fintype M2] [DecidableEq C]
    [DecidableEq D] (Kd Kc K2 V lam : ℕ) (hN : 2 ^ lam < Fintype.card S)
    (hKd : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ Kd)
    (hKc : ∀ c : C, (univ.filter fun s => H.chop s = c).card ≤ Kc)
    (hK2 : Fintype.card R * Fintype.card M2 ≤ K2)
    (hV : Fintype.card X1 ≤ V)
    (hlev : 2 ^ lam * (2 ^ lam * (Kd + 2 * Kc + K2) + 2 * V) ≤
      2 * (Fintype.card S - 2 ^ lam))
    (A : Strat S ((X1 × R × M2) × (X1 × R × M2))) (Q : ℕ) :
    (H.collisionGame A).prob PState.init (fun r s' => Wins r ∧ s'.count ≤ Q) ≤
      min 1 (((Q : ℝ) + 1) / 2 ^ lam) := by
  refine le_min_one_of_level (Strat.prob_le_one _ _ _) fun hQ => ?_
  exact (H.collision_bound Kd Kc K2 V Q (lt_of_le_of_lt hQ hN) hKd hKc hK2 hV A).trans
    (unionBound_le_level _ _ V Q lam hQ hN hlev)

set_option exponentiation.threshold 2000 in
/-- **120-bit binding of the leaf hash at the design's sizes.** State 1,600 bits; first call
`0^128 ‖ tag ‖ m[0..176)`, so `2^1472` valid first-call inputs; chaining value 832 bits, so
`2^768` states per chaining value and `2^768 = 2^128 · 2^640` second-call inputs per chaining
slot; digest `dBits ≥ 240` bits, so at most `2^1360` states per digest. Then for every adversary
and every query budget `Q`, the probability of two different leaf inputs with one digest within
`Q` queries is at most `min 1 ((Q + 1) / 2^120)`. -/
theorem binding_1600 [Fintype X1] [Fintype R] [Fintype M2] [DecidableEq C] [DecidableEq D]
    (hS : Fintype.card S = 2 ^ 1600)
    (hX1 : Fintype.card X1 ≤ 2 ^ 1472)
    (hR : Fintype.card R * Fintype.card M2 ≤ 2 ^ 768)
    (hKc : ∀ c : C, (univ.filter fun s => H.chop s = c).card ≤ 2 ^ 768)
    (hKd : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ 2 ^ 1360)
    (A : Strat S ((X1 × R × M2) × (X1 × R × M2))) (Q : ℕ) :
    (H.collisionGame A).prob PState.init (fun r s' => Wins r ∧ s'.count ≤ Q) ≤
      min 1 (((Q : ℝ) + 1) / 2 ^ 120) := by
  refine H.collision_bound_level (2 ^ 1360) (2 ^ 768) (2 ^ 768) (2 ^ 1472) 120 ?_ hKd hKc hR hX1
    ?_ A Q
  · rw [hS]
    norm_num
  · rw [hS]
    norm_num

end TwoCall

end CommitGolfCandidate.Permutation
