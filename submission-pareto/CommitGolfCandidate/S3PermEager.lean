import CommitGolfCandidate.S3PermModel
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic

/-! Eager runs of a strategy against one fixed permutation, and the identity between the
average over all permutations and the lazily sampled table of `S3PermModel`.

`Strat.eager π st s f` runs `st` with every query answered by `π`, keeping the same table
and counter as the lazy run. `Trace.ext t` is the set of permutations that agree with the
table `t`. `Strat.sum_eager`: summing the eager runs over `ext t` gives `|ext t|` times the
lazy expectation from `t`. With the empty table this is `Strat.avg_eager`. -/

set_option linter.unusedSectionVars false

namespace CommitGolfCandidate.Permutation

open Finset

variable {S : Type} [Fintype S] [DecidableEq S]

namespace Trace

open Classical in
/-- The permutations that agree with every entry of the table. -/
noncomputable def ext (t : Trace S) : Finset (Equiv.Perm S) :=
  Finset.univ.filter fun π => ∀ e ∈ t, π e.inp = e.out

theorem mem_ext {t : Trace S} {π : Equiv.Perm S} : π ∈ t.ext ↔ ∀ e ∈ t, π e.inp = e.out := by
  simp [ext]

theorem ext_nil : Trace.ext ([] : Trace S) = Finset.univ := by
  ext π
  simp [mem_ext]

theorem mem_ext_cons {t : Trace S} {e : Entry S} {π : Equiv.Perm S} :
    π ∈ ext (e :: t) ↔ π e.inp = e.out ∧ π ∈ t.ext := by
  simp [mem_ext]

/-- A consistent permutation maps an unused input to an unused output. -/
theorem apply_mem_freeOut {t : Trace S} {π : Equiv.Perm S} (hπ : π ∈ t.ext) {x : S}
    (hx : x ∉ t.usedIn) : π x ∈ t.freeOut := by
  rw [mem_freeOut, mem_usedOut]
  rintro ⟨e, he, heq⟩
  apply hx
  rw [mem_usedIn]
  refine ⟨e, he, ?_⟩
  have h := mem_ext.1 hπ e he
  exact π.injective (h.trans heq)

/-- A consistent permutation maps an unused output back to an unused input. -/
theorem symm_apply_mem_freeIn {t : Trace S} {π : Equiv.Perm S} (hπ : π ∈ t.ext) {y : S}
    (hy : y ∉ t.usedOut) : π.symm y ∈ t.freeIn := by
  rw [mem_freeIn, mem_usedIn]
  rintro ⟨e, he, heq⟩
  apply hy
  rw [mem_usedOut]
  refine ⟨e, he, ?_⟩
  have h := mem_ext.1 hπ e he
  rw [← h, heq, Equiv.apply_symm_apply]

theorem card_ext_cons_out_le {t : Trace S} (d : Dir) (x y y' : S) (hy : y ∉ t.usedOut)
    (hy' : y' ∉ t.usedOut) :
    (ext (⟨d, x, y⟩ :: t)).card ≤ (ext (⟨d, x, y'⟩ :: t)).card := by
  refine Finset.card_le_card_of_injOn (fun π => Equiv.swap y y' * π) ?_ ?_
  · intro π hπ
    have hπ' := mem_ext_cons.1 (Finset.mem_coe.1 hπ)
    refine Finset.mem_coe.2 (mem_ext_cons.2 ⟨?_, mem_ext.2 fun e he => ?_⟩)
    · show Equiv.swap y y' (π x) = y'
      have h1 : π x = y := hπ'.1
      rw [h1, Equiv.swap_apply_left]
    · show Equiv.swap y y' (π e.inp) = e.out
      rw [mem_ext.1 hπ'.2 e he]
      refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
      · rintro rfl
        exact hy (mem_usedOut.2 ⟨e, he, rfl⟩)
      · rintro rfl
        exact hy' (mem_usedOut.2 ⟨e, he, rfl⟩)
  · intro π _ π' _ h
    exact mul_left_cancel h

theorem card_ext_cons_out {t : Trace S} (d : Dir) (x y y' : S) (hy : y ∉ t.usedOut)
    (hy' : y' ∉ t.usedOut) :
    (ext (⟨d, x, y⟩ :: t)).card = (ext (⟨d, x, y'⟩ :: t)).card :=
  le_antisymm (card_ext_cons_out_le d x y y' hy hy') (card_ext_cons_out_le d x y' y hy' hy)

theorem card_ext_cons_inp_le {t : Trace S} (d : Dir) (x x' y : S) (hx : x ∉ t.usedIn)
    (hx' : x' ∉ t.usedIn) :
    (ext (⟨d, x, y⟩ :: t)).card ≤ (ext (⟨d, x', y⟩ :: t)).card := by
  refine Finset.card_le_card_of_injOn (fun π => π * Equiv.swap x x') ?_ ?_
  · intro π hπ
    have hπ' := mem_ext_cons.1 (Finset.mem_coe.1 hπ)
    refine Finset.mem_coe.2 (mem_ext_cons.2 ⟨?_, mem_ext.2 fun e he => ?_⟩)
    · show π (Equiv.swap x x' x') = y
      rw [Equiv.swap_apply_right]
      exact hπ'.1
    · show π (Equiv.swap x x' e.inp) = e.out
      rw [Equiv.swap_apply_of_ne_of_ne]
      · exact mem_ext.1 hπ'.2 e he
      · intro h
        exact hx (mem_usedIn.2 ⟨e, he, h⟩)
      · intro h
        exact hx' (mem_usedIn.2 ⟨e, he, h⟩)
  · intro π _ π' _ h
    exact mul_right_cancel h

theorem card_ext_cons_inp {t : Trace S} (d : Dir) (x x' y : S) (hx : x ∉ t.usedIn)
    (hx' : x' ∉ t.usedIn) :
    (ext (⟨d, x, y⟩ :: t)).card = (ext (⟨d, x', y⟩ :: t)).card :=
  le_antisymm (card_ext_cons_inp_le d x x' y hx hx') (card_ext_cons_inp_le d x' x y hx' hx)

/-- Split the consistent permutations by the image of an unused input. -/
theorem sum_ext_fwd {t : Trace S} {x : S} (hx : x ∉ t.usedIn) (d : Dir)
    (G : Equiv.Perm S → ℝ) :
    ∑ π ∈ t.ext, G π = ∑ y ∈ t.freeOut, ∑ π ∈ ext (⟨d, x, y⟩ :: t), G π := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun π : Equiv.Perm S => π x) (t := t.freeOut)
    (fun π hπ => apply_mem_freeOut hπ hx)]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext π
  simp only [Finset.mem_filter, mem_ext_cons]
  exact and_comm

/-- Split the consistent permutations by the preimage of an unused output. -/
theorem sum_ext_inv {t : Trace S} {y : S} (hy : y ∉ t.usedOut) (d : Dir)
    (G : Equiv.Perm S → ℝ) :
    ∑ π ∈ t.ext, G π = ∑ x ∈ t.freeIn, ∑ π ∈ ext (⟨d, x, y⟩ :: t), G π := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun π : Equiv.Perm S => π.symm y) (t := t.freeIn)
    (fun π hπ => symm_apply_mem_freeIn hπ hy)]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext π
  simp only [Finset.mem_filter, mem_ext_cons]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [← h2, Equiv.apply_symm_apply], h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by rw [← h1, Equiv.symm_apply_apply]⟩

theorem WF.fwdHits_eq {t : Trace S} (h : WF t) {e : Entry S} (he : e ∈ t) :
    t.fwdHits e.inp = {e.out} := by
  ext y
  rw [mem_fwdHits, Finset.mem_singleton]
  constructor
  · rintro ⟨e', he', h1, h2⟩
    rw [← h2, h.inp_inj he' he h1]
  · rintro rfl
    exact ⟨e, he, rfl, rfl⟩

theorem WF.invHits_eq {t : Trace S} (h : WF t) {e : Entry S} (he : e ∈ t) :
    t.invHits e.out = {e.inp} := by
  ext x
  rw [mem_invHits, Finset.mem_singleton]
  constructor
  · rintro ⟨e', he', h1, h2⟩
    rw [← h2, h.out_inj he' he h1]
  · rintro rfl
    exact ⟨e, he, rfl, rfl⟩

end Trace

theorem avg_singleton {ι : Type} (a : ι) (g : ι → ℝ) : avg {a} g = g a := by
  simp [avg]

/-- A sum with equal weights on a finite set is the total weight times the average. -/
theorem sum_weight_eq {ι : Type} (A : Finset ι) (w : ι → ℝ) (g : ι → ℝ) (c : ℝ)
    (hw : ∀ i ∈ A, w i = c) :
    ∑ i ∈ A, w i * g i = (∑ i ∈ A, w i) * avg A g := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [avg]
  · have hpos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    rw [Finset.sum_congr rfl fun i hi => by rw [hw i hi],
      Finset.sum_congr rfl fun i hi => hw i hi, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul]
    unfold avg
    field_simp

namespace Strat

variable {α : Type}

/-- Run the strategy with every query answered by the fixed permutation `π`, with the same
table and counter bookkeeping as the lazy run. Coins are averaged. -/
noncomputable def eager (π : Equiv.Perm S) : Strat S α → PState S → (α → PState S → ℝ) → ℝ
  | .done a, s, f => f a s
  | .fwd x k, s, f => (k (π x)).eager π ⟨s.trace.stepF x (π x), s.count + 1⟩ f
  | .inv y k, s, f => (k (π.symm y)).eager π ⟨s.trace.stepI (π.symm y) y, s.count + 1⟩ f
  | .rand _ k, s, f => avg Finset.univ fun i => (k i).eager π s f

theorem eager_nonneg (π : Equiv.Perm S) {f : α → PState S → ℝ} (h : ∀ a s, 0 ≤ f a s)
    (st : Strat S α) (s : PState S) : 0 ≤ st.eager π s f := by
  induction st generalizing s with
  | done a => exact h a s
  | fwd x k ih => exact ih _ _
  | inv y k ih => exact ih _ _
  | rand n k ih => exact avg_nonneg fun i _ => ih i _

/-- **Eager = lazy.** Summing the eager runs over the permutations consistent with a
well-formed table gives their number times the lazy expectation from that table. -/
theorem sum_eager (st : Strat S α) (s : PState S) (hs : s.trace.WF) (f : α → PState S → ℝ) :
    ∑ π ∈ s.trace.ext, st.eager π s f = (s.trace.ext.card : ℝ) * st.exp s f := by
  induction st generalizing s with
  | done a =>
    simp only [eager, exp, Finset.sum_const, nsmul_eq_mul]
  | rand n k ih =>
    simp only [eager, exp]
    rw [← avg_sum, avg_congr fun i _ => ih i s hs, avg_mul_left]
  | fwd x k ih =>
    obtain ⟨t, c⟩ := s
    simp only at hs
    simp only [eager, exp]
    by_cases hx : x ∈ t.usedIn
    · obtain ⟨e, he, rfl⟩ := Trace.mem_usedIn.1 hx
      have step : t.stepF e.inp e.out = t := by
        unfold Trace.stepF
        rw [if_pos hx]
      have lhs : ∑ π ∈ t.ext, (k (π e.inp)).eager π ⟨t.stepF e.inp (π e.inp), c + 1⟩ f =
          ∑ π ∈ t.ext, (k e.out).eager π ⟨t, c + 1⟩ f := by
        refine Finset.sum_congr rfl fun π hπ => ?_
        rw [Trace.mem_ext.1 hπ e he, step]
      rw [lhs, ih e.out ⟨t, c + 1⟩ hs]
      have ans : t.fwdAns e.inp = {e.out} := by
        unfold Trace.fwdAns
        rw [if_pos hx, hs.fwdHits_eq he]
      rw [ans, avg_singleton, step]
    · have lhs : ∑ π ∈ t.ext, (k (π x)).eager π ⟨t.stepF x (π x), c + 1⟩ f =
          ∑ y ∈ t.freeOut, ((Trace.ext (⟨.fwd, x, y⟩ :: t)).card : ℝ) *
            (k y).exp ⟨⟨.fwd, x, y⟩ :: t, c + 1⟩ f := by
        rw [Trace.sum_ext_fwd hx .fwd]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [← ih y ⟨⟨.fwd, x, y⟩ :: t, c + 1⟩ (hs.cons hx (Trace.mem_freeOut.1 hy))]
        refine Finset.sum_congr rfl fun π hπ => ?_
        have hπx : π x = y := (Trace.mem_ext_cons.1 hπ).1
        have step : t.stepF x y = ⟨.fwd, x, y⟩ :: t := by
          unfold Trace.stepF
          rw [if_neg hx]
        rw [hπx, step]
      have ans : t.fwdAns x = t.freeOut := by
        unfold Trace.fwdAns
        rw [if_neg hx]
      have rhs : avg (t.fwdAns x) (fun y => (k y).exp ⟨t.stepF x y, c + 1⟩ f) =
          avg t.freeOut (fun y => (k y).exp ⟨⟨.fwd, x, y⟩ :: t, c + 1⟩ f) := by
        rw [ans]
        refine avg_congr fun y _ => ?_
        unfold Trace.stepF
        rw [if_neg hx]
      have total : (t.ext.card : ℝ) =
          ∑ y ∈ t.freeOut, ((Trace.ext (⟨.fwd, x, y⟩ :: t)).card : ℝ) := by
        have h := Trace.sum_ext_fwd hx .fwd (fun _ : Equiv.Perm S => (1 : ℝ))
        simpa using h
      rw [lhs, rhs, total]
      rcases t.freeOut.eq_empty_or_nonempty with hempty | ⟨y0, hy0⟩
      · rw [hempty]
        simp [avg]
      · exact sum_weight_eq _ _ _ ((Trace.ext (⟨.fwd, x, y0⟩ :: t)).card : ℝ) fun y hy => by
          rw [Trace.card_ext_cons_out .fwd x y y0 (Trace.mem_freeOut.1 hy)
            (Trace.mem_freeOut.1 hy0)]
  | inv y k ih =>
    obtain ⟨t, c⟩ := s
    simp only at hs
    simp only [eager, exp]
    by_cases hy : y ∈ t.usedOut
    · obtain ⟨e, he, rfl⟩ := Trace.mem_usedOut.1 hy
      have step : t.stepI e.inp e.out = t := by
        unfold Trace.stepI
        rw [if_pos hy]
      have lhs : ∑ π ∈ t.ext,
            (k (π.symm e.out)).eager π ⟨t.stepI (π.symm e.out) e.out, c + 1⟩ f =
          ∑ π ∈ t.ext, (k e.inp).eager π ⟨t, c + 1⟩ f := by
        refine Finset.sum_congr rfl fun π hπ => ?_
        have hsymm : π.symm e.out = e.inp := by
          rw [← Trace.mem_ext.1 hπ e he, Equiv.symm_apply_apply]
        rw [hsymm, step]
      rw [lhs, ih e.inp ⟨t, c + 1⟩ hs]
      have ans : t.invAns e.out = {e.inp} := by
        unfold Trace.invAns
        rw [if_pos hy, hs.invHits_eq he]
      rw [ans, avg_singleton, step]
    · have lhs : ∑ π ∈ t.ext, (k (π.symm y)).eager π ⟨t.stepI (π.symm y) y, c + 1⟩ f =
          ∑ x ∈ t.freeIn, ((Trace.ext (⟨.inv, x, y⟩ :: t)).card : ℝ) *
            (k x).exp ⟨⟨.inv, x, y⟩ :: t, c + 1⟩ f := by
        rw [Trace.sum_ext_inv hy .inv]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [← ih x ⟨⟨.inv, x, y⟩ :: t, c + 1⟩ (hs.cons (Trace.mem_freeIn.1 hx) hy)]
        refine Finset.sum_congr rfl fun π hπ => ?_
        have hπx : π.symm y = x := by
          have h1 : π x = y := (Trace.mem_ext_cons.1 hπ).1
          rw [← h1, Equiv.symm_apply_apply]
        have step : t.stepI x y = ⟨.inv, x, y⟩ :: t := by
          unfold Trace.stepI
          rw [if_neg hy]
        rw [hπx, step]
      have ans : t.invAns y = t.freeIn := by
        unfold Trace.invAns
        rw [if_neg hy]
      have rhs : avg (t.invAns y) (fun x => (k x).exp ⟨t.stepI x y, c + 1⟩ f) =
          avg t.freeIn (fun x => (k x).exp ⟨⟨.inv, x, y⟩ :: t, c + 1⟩ f) := by
        rw [ans]
        refine avg_congr fun x _ => ?_
        unfold Trace.stepI
        rw [if_neg hy]
      have total : (t.ext.card : ℝ) =
          ∑ x ∈ t.freeIn, ((Trace.ext (⟨.inv, x, y⟩ :: t)).card : ℝ) := by
        have h := Trace.sum_ext_inv hy .inv (fun _ : Equiv.Perm S => (1 : ℝ))
        simpa using h
      rw [lhs, rhs, total]
      rcases t.freeIn.eq_empty_or_nonempty with hempty | ⟨x0, hx0⟩
      · rw [hempty]
        simp [avg]
      · exact sum_weight_eq _ _ _ ((Trace.ext (⟨.inv, x0, y⟩ :: t)).card : ℝ) fun x hx => by
          rw [Trace.card_ext_cons_inp .inv x x0 y (Trace.mem_freeIn.1 hx)
            (Trace.mem_freeIn.1 hx0)]

/-- Averaging the eager runs over all permutations gives the lazy expectation. -/
theorem avg_eager (st : Strat S α) (f : α → PState S → ℝ) :
    avg Finset.univ (fun π : Equiv.Perm S => st.eager π PState.init f) =
      st.exp PState.init f := by
  have h := sum_eager st PState.init Trace.WF.nil f
  simp only [PState.init, Trace.ext_nil] at h
  unfold avg
  simp only [PState.init]
  rw [h]
  have hpos : (0 : ℝ) < (Finset.univ : Finset (Equiv.Perm S)).card := by
    exact_mod_cast Finset.card_pos.2 ⟨1, Finset.mem_univ _⟩
  field_simp

end Strat

end CommitGolfCandidate.Permutation
