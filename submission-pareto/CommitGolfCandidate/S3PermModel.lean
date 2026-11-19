import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic

/-!
# A lazily sampled ideal permutation with forward and inverse queries

This file is self-contained on Mathlib (the pinned VCVio revision has no random-permutation
module). It defines

* `Trace S`: the table of a lazily sampled permutation of the finite type `S`, as a list of
  entries `(direction, input, output)`, newest first. An entry is created only by a *fresh*
  query; its direction records whether the pair was fixed by a forward query (the output was
  sampled) or by an inverse query (the input was sampled). `Trace.WF` says the table is a partial
  bijection.
* `PState S`: the table together with a counter of all queries, repeated ones included.
* `Strat S α`: an adaptive strategy (adversary or game): a tree whose nodes are forward queries,
  inverse queries and private coin tosses, and whose leaves carry the result.
* `Strat.exp st s f`: the expectation of `f result finalState` when `st` is run from state `s`
  against the lazy permutation: a fresh forward query is answered uniformly from the unused
  outputs, a fresh inverse query uniformly from the unused inputs, a repeated query from the
  table. `Strat.prob` is the probability of an event.
* `Strat.post st s P`: `P` holds for every result and final state that the run can reach.
* `Strat.QB st n`: `st` makes at most `n` permutation queries on every path.

Everything else in this directory is proved from these definitions.
-/

set_option linter.unusedSectionVars false

namespace CommitGolfCandidate.Permutation

open Finset

/-! ### Averages over a finite set -/

/-- The average of `g` over the finite set `A` (zero when `A` is empty). -/
noncomputable def avg {ι : Type} (A : Finset ι) (g : ι → ℝ) : ℝ := (∑ i ∈ A, g i) / (A.card : ℝ)

section avg
variable {ι : Type} {A : Finset ι} {g h : ι → ℝ}

theorem avg_mono (hgh : ∀ i ∈ A, g i ≤ h i) : avg A g ≤ avg A h :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum hgh) (Nat.cast_nonneg _)

theorem avg_nonneg (hg : ∀ i ∈ A, 0 ≤ g i) : 0 ≤ avg A g :=
  div_nonneg (Finset.sum_nonneg hg) (Nat.cast_nonneg _)

theorem avg_le {c : ℝ} (hc : 0 ≤ c) (hg : ∀ i ∈ A, g i ≤ c) : avg A g ≤ c := by
  unfold avg
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simpa using hc
  · have hpos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    rw [div_le_iff₀ hpos]
    calc ∑ i ∈ A, g i ≤ ∑ _i ∈ A, c := Finset.sum_le_sum hg
      _ = c * A.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem avg_const (hA : A.Nonempty) (c : ℝ) : avg A (fun _ => c) = c := by
  unfold avg
  have hpos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem avg_zero : avg A (fun _ => (0 : ℝ)) = 0 := by simp [avg]

theorem avg_add : avg A (fun i => g i + h i) = avg A g + avg A h := by
  simp [avg, Finset.sum_add_distrib, add_div]

theorem avg_mul_left (c : ℝ) : avg A (fun i => c * g i) = c * avg A g := by
  simp [avg, ← Finset.mul_sum, mul_div_assoc]

theorem avg_sum {κ : Type} (I : Finset κ) (G : κ → ι → ℝ) :
    avg A (fun i => ∑ j ∈ I, G j i) = ∑ j ∈ I, avg A (G j) := by
  unfold avg
  rw [Finset.sum_comm, Finset.sum_div]

theorem avg_congr (hgh : ∀ i ∈ A, g i = h i) : avg A g = avg A h := by
  unfold avg
  rw [Finset.sum_congr rfl hgh]

end avg

/-! ### Indicators -/

open Classical in
/-- The indicator of a proposition, as a real number. -/
noncomputable def ind (p : Prop) : ℝ := if p then 1 else 0

theorem ind_pos {p : Prop} (h : p) : ind p = 1 := if_pos h

theorem ind_neg {p : Prop} (h : ¬ p) : ind p = 0 := if_neg h

theorem ind_nonneg (p : Prop) : 0 ≤ ind p := by
  unfold ind
  split_ifs <;> norm_num

theorem ind_le_one (p : Prop) : ind p ≤ 1 := by
  unfold ind
  split_ifs <;> norm_num

theorem ind_mono {p q : Prop} (h : p → q) : ind p ≤ ind q := by
  by_cases hp : p
  · rw [ind_pos hp, ind_pos (h hp)]
  · rw [ind_neg hp]
    exact ind_nonneg q

open Classical in
theorem sum_ind {ι : Type} (A : Finset ι) (p : ι → Prop) :
    ∑ i ∈ A, ind (p i) = ((A.filter p).card : ℝ) := by
  unfold ind
  rw [Finset.sum_boole]

/-- If every `i` with `p i` lies in a set of at most `n` elements, the indicators sum to at most
`n`. -/
theorem sum_ind_le {ι : Type} (A F : Finset ι) (p : ι → Prop) (h : ∀ i ∈ A, p i → i ∈ F) :
    ∑ i ∈ A, ind (p i) ≤ (F.card : ℝ) := by
  classical
  rw [sum_ind]
  exact_mod_cast Finset.card_le_card fun i hi =>
    h i (Finset.mem_filter.1 hi).1 (Finset.mem_filter.1 hi).2

/-! ### The table -/

/-- Which kind of fresh query created a table entry. -/
inductive Dir
  | fwd
  | inv
  deriving DecidableEq

/-- One table entry: the permutation maps `inp` to `out`. For `dir = .fwd` the adversary chose
`inp` and `out` was sampled; for `dir = .inv` the adversary chose `out` and `inp` was sampled. -/
structure Entry (S : Type) where
  dir : Dir
  inp : S
  out : S
  deriving DecidableEq

/-- The table of the lazily sampled permutation, newest entry first. -/
abbrev Trace (S : Type) := List (Entry S)

namespace Trace
variable {S : Type} [DecidableEq S]

/-- Inputs that already have an image. -/
def usedIn (t : Trace S) : Finset S := (t.map Entry.inp).toFinset

/-- Outputs that already have a preimage. -/
def usedOut (t : Trace S) : Finset S := (t.map Entry.out).toFinset

/-- The stored images of `x` (a singleton or empty for a well-formed table). -/
def fwdHits (t : Trace S) (x : S) : Finset S :=
  ((t.filter fun e => e.inp = x).map Entry.out).toFinset

/-- The stored preimages of `y`. -/
def invHits (t : Trace S) (y : S) : Finset S :=
  ((t.filter fun e => e.out = y).map Entry.inp).toFinset

@[simp] theorem mem_usedIn {t : Trace S} {x : S} : x ∈ t.usedIn ↔ ∃ e ∈ t, e.inp = x := by
  simp [usedIn]

@[simp] theorem mem_usedOut {t : Trace S} {y : S} : y ∈ t.usedOut ↔ ∃ e ∈ t, e.out = y := by
  simp [usedOut]

@[simp] theorem mem_fwdHits {t : Trace S} {x y : S} :
    y ∈ t.fwdHits x ↔ ∃ e ∈ t, e.inp = x ∧ e.out = y := by
  simp [fwdHits, and_assoc]

@[simp] theorem mem_invHits {t : Trace S} {x y : S} :
    x ∈ t.invHits y ↔ ∃ e ∈ t, e.out = y ∧ e.inp = x := by
  simp [invHits, and_assoc]

/-- The table is a partial bijection: no input and no output occurs twice. -/
structure WF (t : Trace S) : Prop where
  inp : (t.map Entry.inp).Nodup
  out : (t.map Entry.out).Nodup

theorem WF.nil : WF ([] : Trace S) := ⟨by simp, by simp⟩

theorem WF.cons {t : Trace S} {e : Entry S} (h : WF t) (hi : e.inp ∉ t.usedIn)
    (ho : e.out ∉ t.usedOut) : WF (e :: t) := by
  refine ⟨?_, ?_⟩
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨by simpa [usedIn] using hi, h.inp⟩
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨by simpa [usedOut] using ho, h.out⟩

theorem WF.of_cons {t : Trace S} {e : Entry S} (h : WF (e :: t)) :
    WF t ∧ e.inp ∉ t.usedIn ∧ e.out ∉ t.usedOut := by
  have h1 := h.inp
  have h2 := h.out
  rw [List.map_cons, List.nodup_cons] at h1 h2
  exact ⟨⟨h1.2, h2.2⟩, by simpa [usedIn] using h1.1, by simpa [usedOut] using h2.1⟩

theorem WF.card_usedIn {t : Trace S} (h : WF t) : t.usedIn.card = t.length := by
  rw [usedIn, List.toFinset_card_of_nodup h.inp, List.length_map]

theorem WF.card_usedOut {t : Trace S} (h : WF t) : t.usedOut.card = t.length := by
  rw [usedOut, List.toFinset_card_of_nodup h.out, List.length_map]

theorem WF.inp_inj {t : Trace S} (h : WF t) {e e' : Entry S} (he : e ∈ t) (he' : e' ∈ t)
    (hx : e.inp = e'.inp) : e = e' :=
  List.inj_on_of_nodup_map h.inp he he' hx

theorem WF.out_inj {t : Trace S} (h : WF t) {e e' : Entry S} (he : e ∈ t) (he' : e' ∈ t)
    (hy : e.out = e'.out) : e = e' :=
  List.inj_on_of_nodup_map h.out he he' hy

variable [Fintype S]

/-- Inputs without an image yet. -/
def freeIn (t : Trace S) : Finset S := t.usedInᶜ

/-- Outputs without a preimage yet. -/
def freeOut (t : Trace S) : Finset S := t.usedOutᶜ

/-- The possible answers to the forward query `x`: the stored image if there is one, otherwise
every unused output. -/
def fwdAns (t : Trace S) (x : S) : Finset S := if x ∈ t.usedIn then t.fwdHits x else t.freeOut

/-- The possible answers to the inverse query `y`. -/
def invAns (t : Trace S) (y : S) : Finset S := if y ∈ t.usedOut then t.invHits y else t.freeIn

/-- The table after the forward query `x` was answered by `y`. -/
def stepF (t : Trace S) (x y : S) : Trace S := if x ∈ t.usedIn then t else ⟨.fwd, x, y⟩ :: t

/-- The table after the inverse query `y` was answered by `x`. -/
def stepI (t : Trace S) (x y : S) : Trace S := if y ∈ t.usedOut then t else ⟨.inv, x, y⟩ :: t

@[simp] theorem mem_freeIn {t : Trace S} {x : S} : x ∈ t.freeIn ↔ x ∉ t.usedIn := by
  simp [freeIn]

@[simp] theorem mem_freeOut {t : Trace S} {y : S} : y ∈ t.freeOut ↔ y ∉ t.usedOut := by
  simp [freeOut]

theorem WF.length_le {t : Trace S} (h : WF t) : t.length ≤ Fintype.card S :=
  h.card_usedIn ▸ Finset.card_le_univ _

theorem WF.card_freeOut {t : Trace S} (h : WF t) :
    t.freeOut.card = Fintype.card S - t.length := by
  rw [freeOut, Finset.card_compl, h.card_usedOut]

theorem WF.card_freeIn {t : Trace S} (h : WF t) :
    t.freeIn.card = Fintype.card S - t.length := by
  rw [freeIn, Finset.card_compl, h.card_usedIn]

theorem WF.length_lt_of_not_mem_usedIn {t : Trace S} (h : WF t) {x : S} (hx : x ∉ t.usedIn) :
    t.length < Fintype.card S := by
  rw [← h.card_usedIn]
  exact Finset.card_lt_univ_of_notMem hx

theorem WF.length_lt_of_not_mem_usedOut {t : Trace S} (h : WF t) {y : S} (hy : y ∉ t.usedOut) :
    t.length < Fintype.card S := by
  rw [← h.card_usedOut]
  exact Finset.card_lt_univ_of_notMem hy

theorem WF.fwdAns_nonempty {t : Trace S} (h : WF t) (x : S) : (t.fwdAns x).Nonempty := by
  unfold fwdAns
  split_ifs with hx
  · obtain ⟨e, he, rfl⟩ := mem_usedIn.1 hx
    exact ⟨e.out, mem_fwdHits.2 ⟨e, he, rfl, rfl⟩⟩
  · rw [← Finset.card_pos, h.card_freeOut]
    have := h.length_lt_of_not_mem_usedIn hx
    omega

theorem WF.invAns_nonempty {t : Trace S} (h : WF t) (y : S) : (t.invAns y).Nonempty := by
  unfold invAns
  split_ifs with hy
  · obtain ⟨e, he, rfl⟩ := mem_usedOut.1 hy
    exact ⟨e.inp, mem_invHits.2 ⟨e, he, rfl, rfl⟩⟩
  · rw [← Finset.card_pos, h.card_freeIn]
    have := h.length_lt_of_not_mem_usedOut hy
    omega

theorem WF.stepF {t : Trace S} (h : WF t) {x y : S} (hy : y ∈ t.fwdAns x) :
    WF (t.stepF x y) := by
  unfold Trace.stepF
  unfold fwdAns at hy
  split_ifs with hx
  · exact h
  · rw [if_neg hx] at hy
    exact h.cons hx (mem_freeOut.1 hy)

theorem WF.stepI {t : Trace S} (h : WF t) {x y : S} (hx : x ∈ t.invAns y) :
    WF (t.stepI x y) := by
  unfold Trace.stepI
  unfold invAns at hx
  split_ifs with hy
  · exact h
  · rw [if_neg hy] at hx
    exact h.cons (mem_freeIn.1 hx) hy

theorem suffix_stepF (t : Trace S) (x y : S) : t <:+ t.stepF x y := by
  unfold stepF
  split_ifs
  · exact List.suffix_refl _
  · exact List.suffix_cons _ _

theorem suffix_stepI (t : Trace S) (x y : S) : t <:+ t.stepI x y := by
  unfold stepI
  split_ifs
  · exact List.suffix_refl _
  · exact List.suffix_cons _ _

theorem length_stepF_le (t : Trace S) (x y : S) : (t.stepF x y).length ≤ t.length + 1 := by
  unfold stepF
  split_ifs <;> simp

theorem length_stepI_le (t : Trace S) (x y : S) : (t.stepI x y).length ≤ t.length + 1 := by
  unfold stepI
  split_ifs <;> simp

/-- After a forward query the table holds the pair that was returned. -/
theorem mem_stepF_of_mem_fwdAns {t : Trace S} {x y : S} (hy : y ∈ t.fwdAns x) :
    ∃ e ∈ t.stepF x y, e.inp = x ∧ e.out = y := by
  unfold stepF
  unfold fwdAns at hy
  split_ifs with hx
  · rw [if_pos hx] at hy
    exact mem_fwdHits.1 hy
  · exact ⟨⟨.fwd, x, y⟩, List.mem_cons_self, rfl, rfl⟩

/-- After an inverse query the table holds the pair that was returned. -/
theorem mem_stepI_of_mem_invAns {t : Trace S} {x y : S} (hx : x ∈ t.invAns y) :
    ∃ e ∈ t.stepI x y, e.inp = x ∧ e.out = y := by
  unfold stepI
  unfold invAns at hx
  split_ifs with hy
  · rw [if_pos hy] at hx
    obtain ⟨e, he, h1, h2⟩ := mem_invHits.1 hx
    exact ⟨e, he, h2, h1⟩
  · exact ⟨⟨.inv, x, y⟩, List.mem_cons_self, rfl, rfl⟩

end Trace

/-- The state of the ideal permutation: its table and the number of queries made so far
(every forward or inverse query counts, repeated ones included; coin tosses do not). -/
structure PState (S : Type) where
  trace : Trace S
  count : ℕ

/-- The initial state: empty table, no queries. -/
def PState.init {S : Type} : PState S := ⟨[], 0⟩

/-! ### Strategies -/

/-- An adaptive strategy with access to the permutation in both directions and to private coins.
`fwd x k` asks for the image of `x` and continues with `k`; `inv y k` asks for the preimage of
`y`; `rand n k` draws a uniform element of `Fin (n + 1)`. -/
inductive Strat (S : Type) (α : Type) : Type where
  | done : α → Strat S α
  | fwd : S → (S → Strat S α) → Strat S α
  | inv : S → (S → Strat S α) → Strat S α
  | rand : (n : ℕ) → (Fin (n + 1) → Strat S α) → Strat S α

namespace Strat
variable {S : Type} {α β : Type}

/-- Sequential composition. -/
def bind : Strat S α → (α → Strat S β) → Strat S β
  | .done a, f => f a
  | .fwd x k, f => .fwd x fun y => (k y).bind f
  | .inv y k, f => .inv y fun x => (k x).bind f
  | .rand n k, f => .rand n fun i => (k i).bind f

instance : Monad (Strat S) where
  pure := .done
  bind := .bind

@[simp] theorem pure_eq (a : α) : (pure a : Strat S α) = .done a := rfl
@[simp] theorem bind_eq (st : Strat S α) (f : α → Strat S β) : st >>= f = st.bind f := rfl

/-- `QB st n`: on every path `st` makes at most `n` permutation queries. -/
inductive QB : Strat S α → ℕ → Prop
  | done (a : α) (n : ℕ) : QB (.done a) n
  | fwd (x : S) (k : S → Strat S α) (n : ℕ) : (∀ y, QB (k y) n) → QB (.fwd x k) (n + 1)
  | inv (y : S) (k : S → Strat S α) (n : ℕ) : (∀ x, QB (k x) n) → QB (.inv y k) (n + 1)
  | rand (m : ℕ) (k : Fin (m + 1) → Strat S α) (n : ℕ) : (∀ i, QB (k i) n) → QB (.rand m k) n

theorem QB.mono {st : Strat S α} {n m : ℕ} (h : QB st n) (hnm : n ≤ m) : QB st m := by
  induction h generalizing m with
  | done a n => exact .done a m
  | fwd x k n _ ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .fwd x k m fun y => ih y (by omega)
  | inv y k n _ ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .inv y k m fun x => ih x (by omega)
  | rand j k n _ ih => exact .rand j k m fun i => ih i hnm

theorem QB.bind {st : Strat S α} {f : α → Strat S β} {n m : ℕ} (h : QB st n)
    (hf : ∀ a, QB (f a) m) : QB (st.bind f) (n + m) := by
  induction h with
  | done a n => exact (hf a).mono (by omega)
  | fwd x k n _ ih =>
    have : n + 1 + m = (n + m) + 1 := by omega
    rw [this]
    exact .fwd x _ _ ih
  | inv y k n _ ih =>
    have : n + 1 + m = (n + m) + 1 := by omega
    rw [this]
    exact .inv y _ _ ih
  | rand j k n _ ih => exact .rand j _ _ ih

variable [Fintype S] [DecidableEq S]

/-- The expectation of `f result finalState` when the strategy runs from state `s` against the
lazily sampled permutation. -/
noncomputable def exp : Strat S α → PState S → (α → PState S → ℝ) → ℝ
  | .done a, s, f => f a s
  | .fwd x k, s, f =>
      avg (s.trace.fwdAns x) fun y => (k y).exp ⟨s.trace.stepF x y, s.count + 1⟩ f
  | .inv y k, s, f =>
      avg (s.trace.invAns y) fun x => (k x).exp ⟨s.trace.stepI x y, s.count + 1⟩ f
  | .rand _ k, s, f => avg Finset.univ fun i => (k i).exp s f

/-- The probability that the run from `s` ends with a result and final state satisfying `E`. -/
noncomputable def prob (st : Strat S α) (s : PState S) (E : α → PState S → Prop) : ℝ :=
  st.exp s fun a s' => ind (E a s')

/-- `post st s P`: every result and final state reachable by running `st` from `s` satisfies
`P`. -/
def post : Strat S α → PState S → (α → PState S → Prop) → Prop
  | .done a, s, P => P a s
  | .fwd x k, s, P => ∀ y ∈ s.trace.fwdAns x, (k y).post ⟨s.trace.stepF x y, s.count + 1⟩ P
  | .inv y k, s, P => ∀ x ∈ s.trace.invAns y, (k x).post ⟨s.trace.stepI x y, s.count + 1⟩ P
  | .rand _ k, s, P => ∀ i, (k i).post s P

/-! ### Basic properties of the expectation -/

theorem exp_mono {f g : α → PState S → ℝ} (h : ∀ a s, f a s ≤ g a s) (st : Strat S α)
    (s : PState S) : st.exp s f ≤ st.exp s g := by
  induction st generalizing s with
  | done a => exact h a s
  | fwd x k ih => exact avg_mono fun y _ => ih y _
  | inv y k ih => exact avg_mono fun x _ => ih x _
  | rand n k ih => exact avg_mono fun i _ => ih i _

theorem exp_nonneg {f : α → PState S → ℝ} (h : ∀ a s, 0 ≤ f a s) (st : Strat S α)
    (s : PState S) : 0 ≤ st.exp s f := by
  induction st generalizing s with
  | done a => exact h a s
  | fwd x k ih => exact avg_nonneg fun y _ => ih y _
  | inv y k ih => exact avg_nonneg fun x _ => ih x _
  | rand n k ih => exact avg_nonneg fun i _ => ih i _

theorem exp_le {f : α → PState S → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ a s, f a s ≤ c)
    (st : Strat S α) (s : PState S) : st.exp s f ≤ c := by
  induction st generalizing s with
  | done a => exact h a s
  | fwd x k ih => exact avg_le hc fun y _ => ih y _
  | inv y k ih => exact avg_le hc fun x _ => ih x _
  | rand n k ih => exact avg_le hc fun i _ => ih i _

theorem exp_zero (st : Strat S α) (s : PState S) : st.exp s (fun _ _ => 0) = 0 := by
  induction st generalizing s with
  | done a => rfl
  | fwd x k ih => simp only [exp, ih, avg_zero]
  | inv y k ih => simp only [exp, ih, avg_zero]
  | rand n k ih => simp only [exp, ih, avg_zero]

theorem exp_add (f g : α → PState S → ℝ) (st : Strat S α) (s : PState S) :
    st.exp s (fun a s' => f a s' + g a s') = st.exp s f + st.exp s g := by
  induction st generalizing s with
  | done a => rfl
  | fwd x k ih => simp only [exp, ih, avg_add]
  | inv y k ih => simp only [exp, ih, avg_add]
  | rand n k ih => simp only [exp, ih, avg_add]

theorem exp_mul_left (c : ℝ) (f : α → PState S → ℝ) (st : Strat S α) (s : PState S) :
    st.exp s (fun a s' => c * f a s') = c * st.exp s f := by
  induction st generalizing s with
  | done a => rfl
  | fwd x k ih => simp only [exp, ih, avg_mul_left]
  | inv y k ih => simp only [exp, ih, avg_mul_left]
  | rand n k ih => simp only [exp, ih, avg_mul_left]

theorem exp_sum {κ : Type} (I : Finset κ) (F : κ → α → PState S → ℝ) (st : Strat S α)
    (s : PState S) :
    st.exp s (fun a s' => ∑ j ∈ I, F j a s') = ∑ j ∈ I, st.exp s (F j) := by
  induction st generalizing s with
  | done a => rfl
  | fwd x k ih => simp only [exp, ih, avg_sum]
  | inv y k ih => simp only [exp, ih, avg_sum]
  | rand n k ih => simp only [exp, ih, avg_sum]

theorem exp_bind (st : Strat S α) (k : α → Strat S β) (s : PState S) (f : β → PState S → ℝ) :
    (st.bind k).exp s f = st.exp s fun a s' => (k a).exp s' f := by
  induction st generalizing s with
  | done a => rfl
  | fwd x k' ih => simp only [bind, exp, ih]
  | inv y k' ih => simp only [bind, exp, ih]
  | rand n k' ih => simp only [bind, exp, ih]

/-! ### Reachability -/

theorem post_mono {P Q : α → PState S → Prop} (h : ∀ a s, P a s → Q a s) {st : Strat S α}
    {s : PState S} (hP : st.post s P) : st.post s Q := by
  induction st generalizing s with
  | done a => exact h a s hP
  | fwd x k ih => exact fun y hy => ih y (hP y hy)
  | inv y k ih => exact fun x hx => ih x (hP x hx)
  | rand n k ih => exact fun i => ih i (hP i)

theorem post_and {P Q : α → PState S → Prop} {st : Strat S α} {s : PState S}
    (hP : st.post s P) (hQ : st.post s Q) : st.post s fun a s' => P a s' ∧ Q a s' := by
  induction st generalizing s with
  | done a => exact ⟨hP, hQ⟩
  | fwd x k ih => exact fun y hy => ih y (hP y hy) (hQ y hy)
  | inv y k ih => exact fun x hx => ih x (hP x hx) (hQ x hx)
  | rand n k ih => exact fun i => ih i (hP i) (hQ i)

theorem post_bind {st : Strat S α} {k : α → Strat S β} {s : PState S}
    {P : β → PState S → Prop} (h : st.post s fun a s' => (k a).post s' P) :
    (st.bind k).post s P := by
  induction st generalizing s with
  | done a => exact h
  | fwd x k' ih => exact fun y hy => ih y (h y hy)
  | inv y k' ih => exact fun x hx => ih x (h x hx)
  | rand n k' ih => exact fun i => ih i (h i)

/-- If `f ≤ g` on everything reachable, the expectations compare. -/
theorem exp_le_exp_of_post {P : α → PState S → Prop} {f g : α → PState S → ℝ}
    {st : Strat S α} {s : PState S} (hP : st.post s P) (h : ∀ a s', P a s' → f a s' ≤ g a s') :
    st.exp s f ≤ st.exp s g := by
  induction st generalizing s with
  | done a => exact h a s hP
  | fwd x k ih => exact avg_mono fun y hy => ih y (hP y hy)
  | inv y k ih => exact avg_mono fun x hx => ih x (hP x hx)
  | rand n k ih => exact avg_mono fun i _ => ih i (hP i)

theorem exp_congr_of_post {P : α → PState S → Prop} {f g : α → PState S → ℝ}
    {st : Strat S α} {s : PState S} (hP : st.post s P) (h : ∀ a s', P a s' → f a s' = g a s') :
    st.exp s f = st.exp s g :=
  le_antisymm (exp_le_exp_of_post hP fun a s' hp => (h a s' hp).le)
    (exp_le_exp_of_post hP fun a s' hp => (h a s' hp).ge)

/-- Invariants of every run: the table stays a partial bijection, it only grows at the front,
and the counter only grows. -/
theorem post_inv (st : Strat S α) (s : PState S) (hs : s.trace.WF) :
    st.post s fun _ s' => s'.trace.WF ∧ s.trace <:+ s'.trace ∧ s.count ≤ s'.count := by
  induction st generalizing s with
  | done a => exact ⟨hs, List.suffix_refl _, le_refl _⟩
  | fwd x k ih =>
    intro y hy
    refine post_mono ?_ (ih y ⟨s.trace.stepF x y, s.count + 1⟩ (hs.stepF hy))
    rintro a s' ⟨h1, h2, h3⟩
    exact ⟨h1, (Trace.suffix_stepF _ _ _).trans h2, by simp only at h3; omega⟩
  | inv y k ih =>
    intro x hx
    refine post_mono ?_ (ih x ⟨s.trace.stepI x y, s.count + 1⟩ (hs.stepI hx))
    rintro a s' ⟨h1, h2, h3⟩
    exact ⟨h1, (Trace.suffix_stepI _ _ _).trans h2, by simp only at h3; omega⟩
  | rand n k ih => exact fun i => ih i s hs

/-- A strategy with at most `n` queries adds at most `n` entries and `n` counts. -/
theorem post_QB {st : Strat S α} {n : ℕ} (h : QB st n) (s : PState S) :
    st.post s fun _ s' => s'.trace.length ≤ s.trace.length + n ∧ s'.count ≤ s.count + n := by
  induction h generalizing s with
  | done a n => exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  | fwd x k n _ ih =>
    intro y _
    refine post_mono ?_ (ih y ⟨s.trace.stepF x y, s.count + 1⟩)
    rintro a s' ⟨h1, h2⟩
    have := Trace.length_stepF_le s.trace x y
    simp only at h1 h2
    exact ⟨by omega, by omega⟩
  | inv y k n _ ih =>
    intro x _
    refine post_mono ?_ (ih x ⟨s.trace.stepI x y, s.count + 1⟩)
    rintro a s' ⟨h1, h2⟩
    have := Trace.length_stepI_le s.trace x y
    simp only at h1 h2
    exact ⟨by omega, by omega⟩
  | rand m k n _ ih => exact fun i => ih i s

/-- Total probability is one from a well-formed state. -/
theorem exp_const (c : ℝ) (st : Strat S α) (s : PState S) (hs : s.trace.WF) :
    st.exp s (fun _ _ => c) = c := by
  induction st generalizing s with
  | done a => rfl
  | fwd x k ih =>
    simp only [exp]
    rw [avg_congr fun y hy => ih y _ (hs.stepF hy)]
    exact avg_const (hs.fwdAns_nonempty x) c
  | inv y k ih =>
    simp only [exp]
    rw [avg_congr fun x hx => ih x _ (hs.stepI hx)]
    exact avg_const (hs.invAns_nonempty y) c
  | rand n k ih =>
    simp only [exp]
    rw [avg_congr fun i _ => ih i s hs]
    exact avg_const Finset.univ_nonempty c

theorem exp_one_sub {f : α → PState S → ℝ} (st : Strat S α) (s : PState S) (hs : s.trace.WF) :
    st.exp s (fun a s' => 1 - f a s') = 1 - st.exp s f := by
  have h := exp_add (fun a s' => 1 - f a s') f st s
  simp only [sub_add_cancel] at h
  rw [exp_const 1 st s hs] at h
  linarith

theorem prob_nonneg (st : Strat S α) (s : PState S) (E : α → PState S → Prop) :
    0 ≤ st.prob s E :=
  exp_nonneg (fun _ _ => ind_nonneg _) st s

theorem prob_le_one (st : Strat S α) (s : PState S) (E : α → PState S → Prop) :
    st.prob s E ≤ 1 :=
  exp_le zero_le_one (fun _ _ => ind_le_one _) st s

/-- Monotonicity of probability on reachable outcomes. -/
theorem prob_le_prob_of_post {P : α → PState S → Prop} {E F : α → PState S → Prop}
    {st : Strat S α} {s : PState S} (hP : st.post s P) (h : ∀ a s', P a s' → E a s' → F a s') :
    st.prob s E ≤ st.prob s F :=
  exp_le_exp_of_post hP fun a s' hp => ind_mono (h a s' hp)

end Strat

end CommitGolfCandidate.Permutation
