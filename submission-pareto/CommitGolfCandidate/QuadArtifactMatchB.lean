import CommitGolf.ArtifactEncoding

/-! A one-pass Boolean comparison of a packed artifact with an ordinary list, and its soundness.
Used to tie the structurally defined commit image to the generated `Artifact` module. -/
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf CommitGolf.ArtifactEncoding

def matchesFrom (bits : Nat) {n : Nat} (p : Packed n) : Nat → List (BitVec bits) → Bool
  | i, [] => i == n
  | i, w :: t => (if h : i < n then p.get bits ⟨i, h⟩ == w else false) && matchesFrom bits p (i+1) t

theorem matches_from_sound (bits : Nat) {n : Nat} (p : Packed n) :
    ∀ (l : List (BitVec bits)) (i : Nat), matchesFrom bits p i l = true →
      i + l.length = n ∧ ∀ (j : Nat) (hj : j < l.length) (h : i + j < n), p.get bits ⟨i+j, h⟩ = l[j]
  | [], i, ok => by
      simp only [matchesFrom, beq_iff_eq] at ok
      exact ⟨by simpa using ok, fun j hj => absurd hj (by simp)⟩
  | w :: t, i, ok => by
      simp only [matchesFrom, Bool.and_eq_true] at ok
      obtain ⟨head, rest⟩ := ok
      obtain ⟨len, eqs⟩ := matches_from_sound bits p t (i+1) rest
      refine ⟨by simp only [List.length_cons]; omega, fun j hj h => ?_⟩
      cases j with
      | zero =>
        have inside : i < n := by omega
        simp only [inside, dite_true, beq_iff_eq] at head
        simpa using head
      | succ j =>
        have e := eqs j (by simp at hj; omega) (by omega)
        simp only [List.getElem_cons_succ]
        rw [← e]
        congr 1
        apply Fin.ext
        simp only
        omega

theorem decode_of_matches (bits : Nat) {n : Nat} (p : Packed n) (l : List (BitVec bits))
    (ok : matchesFrom bits p 0 l = true) : decode bits p = l := by
  obtain ⟨len, eqs⟩ := matches_from_sound bits p l 0 ok
  apply List.ext_getElem
  · simp only [length_decode]; omega
  · intro j h1 h2
    simp only [decode, List.getElem_ofFn]
    have e := eqs j h2 (by omega)
    simp only [Nat.zero_add] at e
    exact e


/-- Element-wise agreement from offset `i`, without the end-of-artifact condition. -/
def prefixMatches (bits : Nat) {n : Nat} (p : Packed n) : Nat → List (BitVec bits) → Bool
  | _, [] => true
  | i, w :: t => (if h : i < n then p.get bits ⟨i, h⟩ == w else false) && prefixMatches bits p (i+1) t

theorem matches_of_prefix (bits : Nat) {n : Nat} (p : Packed n) :
    ∀ (l : List (BitVec bits)) (i : Nat), prefixMatches bits p i l = true → i + l.length = n →
      matchesFrom bits p i l = true
  | [], i, _, len => by simp only [matchesFrom, beq_iff_eq]; simpa using len
  | w :: t, i, ok, len => by
      simp only [prefixMatches, Bool.and_eq_true] at ok
      simp only [matchesFrom, Bool.and_eq_true]
      exact ⟨ok.1, matches_of_prefix bits p t (i+1) ok.2 (by simp only [List.length_cons] at len; omega)⟩

theorem prefix_take_drop (bits : Nat) {n : Nat} (p : Packed n) :
    ∀ (l : List (BitVec bits)) (i m : Nat), prefixMatches bits p i (l.take m) = true →
      prefixMatches bits p (i+m) (l.drop m) = true → prefixMatches bits p i l = true
  | [], _, _, _, _ => rfl
  | w :: t, i, 0, _, rest => by simpa using rest
  | w :: t, i, m+1, head, rest => by
      simp only [List.take_succ_cons, prefixMatches, Bool.and_eq_true] at head
      simp only [prefixMatches, Bool.and_eq_true]
      refine ⟨head.1, prefix_take_drop bits p t (i+1) m head.2 ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm 1 m] using rest

end TwoPermutationPrototype.ArtifactMatchB
