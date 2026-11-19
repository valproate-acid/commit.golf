import CommitGolfCandidate.S3PermUnary

/-!
# The pinned two-call leaf hash: collision resistance

The leaf hash with every size a parameter:

    o1 = π (enc1 x1)                               first call; `enc1` is injective
    o2 = π (enc2 (r, chop o1, pin (enc1 x1), m2))  second call
    digest = trunc o2

Every state may be a first-call input, so no prefix of the first window is fixed. Instead, part
of the first window (`pin`) is repeated in the second window: the two calls of a leaf are tied
by the chaining value `chop o1` and by the pinned part of the first input.

For the stage-3 layout `enc1` is the identity on 200 leaf bytes, `pin` keeps bytes 168..200 of
the first window, `chop` keeps bytes 112..200 of a reply, `enc2 (r, c, p, m) = r ‖ c ‖ p ‖ m` and
`trunc` keeps bytes 0..32 (S3LeafLayout.lean). Nothing below depends on these choices.

Six pair events, named after the role of the fresh entry `new` against an older entry `old`:

* `DigestCollision`: `new` is forward and agrees with `old` on the digest part;
* `ChainCollision`: `new` is forward and agrees with `old` on the chaining part;
* `ForwardHitsSlot`: `new` is forward and its chaining part is the chaining slot of `old.inp`;
* `InverseHitsChain`: `new` is inverse and its input is a second-call input whose chaining slot
  is the chaining part of `old`;
* `InversePinChain`: `new` is inverse, agrees with `old` on the chaining part of the output and
  on the pinned part of the input;
* `InversePinSlot`: `new` is inverse and `old.inp` is a second-call input whose chaining slot
  is the chaining part of `new` and whose pin slot is the pinned part of `new.inp`;

and one unary event: an inverse entry is by itself both calls of a leaf, its input being a
second-call input whose chaining and pin slots are its own chaining part and pinned part.

A fresh forward answer is bad for at most `Kd + 2 Kc` values, a fresh inverse answer for at most
`K2 + 2 Kp` values, and the unary event for at most `K2`; `prob_bad_le_inv` charges the unary
term to inverse queries only.
-/

set_option linter.unusedSectionVars false

namespace CommitGolfCandidate.Permutation

open Finset

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The pinned two-call leaf hash. `X1` is the input of the first call, `R` the salt, `C` the
chaining value, `P` the pinned part of the first input, `M2` the rest of the second message, `D`
the digest. -/
structure PinCall (S X1 R C P M2 D : Type) where
  enc1 : X1 → S
  enc1_inj : Function.Injective enc1
  pin : S → P
  chop : S → C
  enc2 : R × C × P × M2 → S
  enc2_inj : Function.Injective enc2
  trunc : S → D

namespace PinCall

variable {X1 R C P M2 D : Type} (H : PinCall S X1 R C P M2 D)

/-- The bad events of the pinned two-call proof, in the order of the file header. -/
def badSpec : BadSpec S where
  pair new old :=
    (new.dir = .fwd ∧ H.trunc new.out = H.trunc old.out) ∨
    (new.dir = .fwd ∧ H.chop new.out = H.chop old.out) ∨
    (new.dir = .fwd ∧ ∃ r p m, old.inp = H.enc2 (r, H.chop new.out, p, m)) ∨
    (new.dir = .inv ∧ ∃ r p m, new.inp = H.enc2 (r, H.chop old.out, p, m)) ∨
    (new.dir = .inv ∧ H.pin new.inp = H.pin old.inp ∧ H.chop new.out = H.chop old.out) ∨
    (new.dir = .inv ∧ ∃ r m, old.inp = H.enc2 (r, H.chop new.out, H.pin new.inp, m))
  single e := e.dir = .inv ∧ ∃ r m, e.inp = H.enc2 (r, H.chop e.out, H.pin e.inp, m)

/-- The table holds both calls of the leaf hash on input `i = (x1, r, m2)`, and the digest is
`d`. -/
def Evaluates (t : Trace S) (i : X1 × R × M2) (d : D) : Prop :=
  ∃ e1 ∈ t, ∃ e2 ∈ t, e1.inp = H.enc1 i.1 ∧
    e2.inp = H.enc2 (i.2.1, H.chop e1.out, H.pin e1.inp, i.2.2) ∧ H.trunc e2.out = d

theorem Evaluates.mono {t t' : Trace S} {i : X1 × R × M2} {d : D} (h : t <:+ t')
    (he : H.Evaluates t i d) : H.Evaluates t' i d := by
  obtain ⟨e1, he1, e2, he2, h1, h2, h3⟩ := he
  exact ⟨e1, h.subset he1, e2, h.subset he2, h1, h2, h3⟩

/-- **Extraction (deterministic).** If a table holds the four calls of two different leaf inputs
with the same digest, it is not good. No probability and no well-formedness of the table is
needed. -/
theorem collision_imp_bad {t : Trace S} {i i' : X1 × R × M2} {d : D} (hne : i ≠ i')
    (h : H.Evaluates t i d) (h' : H.Evaluates t i' d) : ¬ H.badSpec.Good t := by
  intro hg
  obtain ⟨e1, he1, e2, he2, hx1, hx2, hd⟩ := h
  obtain ⟨e1', he1', e2', he2', hx1', hx2', hd'⟩ := h'
  -- a second-call entry `a2` whose digest part equals that of another entry `b2`, in the case
  -- where `a2` is the newer of the two
  have keyA : ∀ (a1 a2 b2 : Entry S) (j : X1 × R × M2), a1 ∈ t → a2 ∈ t →
      a2.inp = H.enc2 (j.2.1, H.chop a1.out, H.pin a1.inp, j.2.2) →
      H.trunc a2.out = H.trunc b2.out → ¬ H.badSpec.pair a2 b2 → False := by
    intro a1 a2 b2 j ha1 ha2 hj2 htr hnp
    cases hdir : a2.dir with
    | fwd => exact hnp (Or.inl ⟨hdir, htr⟩)
    | inv =>
      by_cases heq : a1 = a2
      · subst heq
        exact hg.not_single ha1 ⟨hdir, j.2.1, j.2.2, hj2⟩
      · rcases hg.not_pair ha2 ha1 (Ne.symm heq) with h | h
        · exact h (Or.inr (Or.inr (Or.inr (Or.inl ⟨hdir, j.2.1, H.pin a1.inp, j.2.2, hj2⟩))))
        · cases hdir1 : a1.dir with
          | fwd => exact h (Or.inr (Or.inr (Or.inl ⟨hdir1, j.2.1, H.pin a1.inp, j.2.2, hj2⟩)))
          | inv => exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hdir1, j.2.1, j.2.2, hj2⟩)))))
  -- a first-call entry `a1` whose chaining part and pinned part equal those of another entry
  -- `b1`, in the case where `a1` is the newer of the two
  have keyB : ∀ (a1 b1 : Entry S), H.chop a1.out = H.chop b1.out → H.pin a1.inp = H.pin b1.inp →
      ¬ H.badSpec.pair a1 b1 → False := by
    intro a1 b1 hch hp hnp
    cases hdir : a1.dir with
    | fwd => exact hnp (Or.inr (Or.inl ⟨hdir, hch⟩))
    | inv => exact hnp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hdir, hp, hch⟩)))))
  by_cases h2 : e2 = e2'
  · have hinp : H.enc2 (i.2.1, H.chop e1.out, H.pin e1.inp, i.2.2) =
        H.enc2 (i'.2.1, H.chop e1'.out, H.pin e1'.inp, i'.2.2) := by rw [← hx2, ← hx2', h2]
    have hinj := H.enc2_inj hinp
    simp only [Prod.mk.injEq] at hinj
    obtain ⟨hr, hc, hp, hm⟩ := hinj
    have hx : i.1 ≠ i'.1 := fun hx => hne (Prod.ext hx (Prod.ext hr hm))
    have he : e1 ≠ e1' := by
      rintro rfl
      exact hx (H.enc1_inj (hx1.symm.trans hx1'))
    rcases hg.not_pair he1 he1' he with h | h
    · exact keyB e1 e1' hc hp h
    · exact keyB e1' e1 hc.symm hp.symm h
  · rcases hg.not_pair he2 he2' h2 with h | h
    · exact keyA e1 e2 e2' i he1 he2 hx2 (hd.trans hd'.symm) h
    · exact keyA e1' e2' e2 i' he1' he2' hx2' (hd'.trans hd.symm) h

/-! ### Evaluation -/

/-- Evaluate the leaf hash with two forward queries. -/
def eval (i : X1 × R × M2) : Strat S D :=
  .fwd (H.enc1 i.1) fun o1 => .fwd (H.enc2 (i.2.1, H.chop o1, H.pin (H.enc1 i.1), i.2.2)) fun o2 =>
    .done (H.trunc o2)

theorem eval_post (i : X1 × R × M2) (s : PState S) (hs : s.trace.WF) :
    (H.eval i).post s fun d s' =>
      s'.trace.WF ∧ s.trace <:+ s'.trace ∧ H.Evaluates s'.trace i d := by
  show (Strat.fwd (H.enc1 i.1) _).post s _
  refine Strat.post_fwd hs fun o1 s1 hwf1 hsuf1 hm1 _ => ?_
  show (Strat.fwd (H.enc2 (i.2.1, H.chop o1, H.pin (H.enc1 i.1), i.2.2)) _).post s1 _
  refine Strat.post_fwd hwf1 fun o2 s2 hwf2 hsuf2 hm2 _ => ?_
  obtain ⟨e1, he1, h11, h12⟩ := hm1
  obtain ⟨e2, he2, h21, h22⟩ := hm2
  exact ⟨hwf2, hsuf1.trans hsuf2, e1, hsuf2.subset he1, e2, he2, h11, by rw [h12, h11]; exact h21,
    by rw [h22]⟩

theorem eval_QB (i : X1 × R × M2) : (H.eval i).QB 2 :=
  .fwd _ _ 1 fun _ => .fwd _ _ 0 fun _ => .done _ 0

theorem eval_IQB (i : X1 × R × M2) : (H.eval i).IQB 0 :=
  .fwd _ _ 0 fun _ => .fwd _ _ 0 fun _ => .done _ 0

/-! ### The probability of the bad events -/

/-- The bad events of the pinned two-call hash, with the unary event charged only to the `n`
inverse queries of the strategy. `Kd`, `Kc` and `Kp` bound the number of states with a given
digest part, chaining part and pinned part, `K2` the number of second-call inputs with a given
chaining slot; `k` bounds the bad answers of a fresh forward query (`Kd + 2 Kc`) and of a fresh
inverse query (`K2 + 2 Kp`) separately. -/
theorem prob_bad_le_inv [Fintype R] [Fintype P] [Fintype M2] [DecidableEq C] [DecidableEq P]
    [DecidableEq D] {α : Type} (Kd Kc Kp K2 k Q : ℕ) (hQ : Q < Fintype.card S)
    (hKd : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ Kd)
    (hKc : ∀ c : C, (univ.filter fun s => H.chop s = c).card ≤ Kc)
    (hKp : ∀ p : P, (univ.filter fun s => H.pin s = p).card ≤ Kp)
    (hK2 : Fintype.card R * Fintype.card P * Fintype.card M2 ≤ K2)
    (hkf : Kd + 2 * Kc ≤ k) (hki : K2 + 2 * Kp ≤ k)
    (st : Strat S α) (n : ℕ) (hn : st.IQB n) :
    st.prob PState.init (fun _ s' => ¬ H.badSpec.Good s'.trace ∧ s'.count ≤ Q) ≤
      ((Q : ℝ) * ((Q : ℝ) - 1) / 2 * k + (n : ℝ) * K2) / ((Fintype.card S : ℝ) - Q) := by
  classical
  have hslot : ∀ c : C, (univ.image fun p : R × P × M2 => H.enc2 (p.1, c, p.2.1, p.2.2)).card ≤
      K2 := by
    intro c
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, ← mul_assoc]
    exact hK2
  refine prob_not_good_le_inv H.badSpec k K2 Q hQ ?_ ?_ ?_ ?_ st n hn
  · intro x old
    refine ⟨(univ.filter fun s => H.trunc s = H.trunc old.out) ∪
      (univ.filter fun s => H.chop s = H.chop old.out) ∪
      (univ.filter fun s => ∃ r p m, old.inp = H.enc2 (r, H.chop s, p, m)), ?_, ?_⟩
    · have h3 : (univ.filter fun s => ∃ r p m, old.inp = H.enc2 (r, H.chop s, p, m)).card ≤
          Kc := by
        rcases (univ.filter fun s => ∃ r p m, old.inp = H.enc2 (r, H.chop s, p, m)
          ).eq_empty_or_nonempty with h0 | ⟨y0, hy0⟩
        · rw [h0]
          exact Nat.zero_le _
        · obtain ⟨r0, p0, m0, h0⟩ := (Finset.mem_filter.1 hy0).2
          refine (Finset.card_le_card fun y hy => ?_).trans (hKc (H.chop y0))
          obtain ⟨r, p, m, h⟩ := (Finset.mem_filter.1 hy).2
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
        (univ.filter fun s => ∃ r p m, old.inp = H.enc2 (r, H.chop s, p, m))
      omega
    · intro y hy
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hy with h | h | h | h | h | h
      · exact Or.inl (Or.inl h.2)
      · exact Or.inl (Or.inr h.2)
      · exact Or.inr h.2
      · exact absurd h.1 (by simp)
      · exact absurd h.1 (by simp)
      · exact absurd h.1 (by simp)
  · intro x y hs
    exact absurd hs.1 (by simp)
  · intro y old
    refine ⟨(univ.image fun p : R × P × M2 => H.enc2 (p.1, H.chop old.out, p.2.1, p.2.2)) ∪
      (univ.filter fun s => H.pin s = H.pin old.inp) ∪
      (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop y, H.pin s, m)), ?_, ?_⟩
    · have h6 : (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop y, H.pin s, m)).card ≤
          Kp := by
        rcases (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop y, H.pin s, m)
          ).eq_empty_or_nonempty with h0 | ⟨x0, hx0⟩
        · rw [h0]
          exact Nat.zero_le _
        · obtain ⟨r0, m0, h0⟩ := (Finset.mem_filter.1 hx0).2
          refine (Finset.card_le_card fun x hx => ?_).trans (hKp (H.pin x0))
          obtain ⟨r, m, h⟩ := (Finset.mem_filter.1 hx).2
          have hinj := H.enc2_inj (h.symm.trans h0)
          simp only [Prod.mk.injEq] at hinj
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hinj.2.2.1⟩
      have := hslot (H.chop old.out)
      have := hKp (H.pin old.inp)
      have h45 := Finset.card_union_le
        (univ.image fun p : R × P × M2 => H.enc2 (p.1, H.chop old.out, p.2.1, p.2.2))
        (univ.filter fun s => H.pin s = H.pin old.inp)
      have h456 := Finset.card_union_le
        ((univ.image fun p : R × P × M2 => H.enc2 (p.1, H.chop old.out, p.2.1, p.2.2)) ∪
          (univ.filter fun s => H.pin s = H.pin old.inp))
        (univ.filter fun s => ∃ r m, old.inp = H.enc2 (r, H.chop y, H.pin s, m))
      omega
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with h | h | h | h | h | h
      · exact absurd h.1 (by simp)
      · exact absurd h.1 (by simp)
      · exact absurd h.1 (by simp)
      · obtain ⟨r, p, m, h⟩ := h.2
        exact Or.inl (Or.inl (Finset.mem_image.2 ⟨(r, p, m), Finset.mem_univ _, h.symm⟩))
      · exact Or.inl (Or.inr h.2.1)
      · exact Or.inr h.2
  · intro y
    refine ⟨univ.image fun p : R × P × M2 => H.enc2 (p.1, H.chop y, p.2.1, p.2.2), hslot _,
      fun x hx => ?_⟩
    obtain ⟨r, m, h⟩ := hx.2
    exact Finset.mem_image.2 ⟨(r, H.pin x, m), Finset.mem_univ _, h.symm⟩

end PinCall

end CommitGolfCandidate.Permutation
