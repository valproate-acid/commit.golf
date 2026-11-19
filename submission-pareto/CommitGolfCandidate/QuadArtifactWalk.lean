import CommitGolfCandidate.QuadArtifactMatchB

/-! Segment-wise artifact comparison: `walk` checks consecutive blocks `g x` of a flattened list at
running offsets and returns the end offset. Each block range is checked by its own kernel
computation, so no declaration has to evaluate a long prefix of the image. -/
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf CommitGolf.ArtifactEncoding

def walk (bits : Nat) {n : Nat} (p : Packed n) {α : Type} (g : α → List (BitVec bits)) :
    Nat → List α → Option Nat
  | i, [] => some i
  | i, x :: xs => if prefixMatches bits p i (g x) then walk bits p g (i + (g x).length) xs else none

theorem prefix_append (bits : Nat) {n : Nat} (p : Packed n) :
    ∀ (a b : List (BitVec bits)) (i : Nat), prefixMatches bits p i a = true →
      prefixMatches bits p (i + a.length) b = true → prefixMatches bits p i (a ++ b) = true
  | [], b, i, _, hb => by simpa using hb
  | w :: t, b, i, ha, hb => by
      simp only [prefixMatches, Bool.and_eq_true] at ha
      simp only [List.cons_append, prefixMatches, Bool.and_eq_true]
      refine ⟨ha.1, prefix_append bits p t b (i+1) ha.2 ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm 1] using hb

theorem walk_sound (bits : Nat) {n : Nat} (p : Packed n) {α : Type} (g : α → List (BitVec bits)) :
    ∀ (l : List α) (i j : Nat), walk bits p g i l = some j →
      prefixMatches bits p i (l.flatMap g) = true ∧ i + (l.flatMap g).length = j
  | [], i, j, h => by simp only [walk, Option.some.injEq] at h; subst h; simp [prefixMatches]
  | x :: xs, i, j, h => by
      simp only [walk] at h
      split at h
      · rename_i head
        obtain ⟨rest, len⟩ := walk_sound bits p g xs _ j h
        refine ⟨?_, ?_⟩
        · simp only [List.flatMap_cons]
          exact prefix_append bits p _ _ i head rest
        · simp only [List.flatMap_cons, List.length_append]; omega
      · cases h

theorem walk_append (bits : Nat) {n : Nat} (p : Packed n) {α : Type} (g : α → List (BitVec bits)) :
    ∀ (a b : List α) (i j k : Nat), walk bits p g i a = some j → walk bits p g j b = some k →
      walk bits p g i (a ++ b) = some k
  | [], b, i, j, k, ha, hb => by simp only [walk, Option.some.injEq] at ha; subst ha; simpa using hb
  | x :: xs, b, i, j, k, ha, hb => by
      simp only [walk] at ha
      simp only [List.cons_append, walk]
      split at ha
      · rename_i head
        simp only [head, if_true]
        exact walk_append bits p g xs b _ j k ha hb
      · cases ha

theorem walk_flatten (bits : Nat) {n : Nat} (p : Packed n) {α : Type} (g : α → List (BitVec bits))
    (l : List α) (i j : Nat) (h : walk bits p g i l = some j) :
    walk bits p id i [l.flatMap g] = some j := by
  obtain ⟨ok, len⟩ := walk_sound bits p g l i j h
  simp only [walk, id, ok, if_true, len]

theorem range'_split : ∀ (s m k : Nat), List.range' s (m + k) = List.range' s m ++ List.range' (s + m) k
  | s, 0, k => by simp
  | s, m+1, k => by
      rw [show m + 1 + k = (m + k) + 1 by omega, List.range'_succ, List.range'_succ, range'_split (s+1) m k,
        show s + 1 + m = s + (m + 1) by omega]
      rfl

theorem replicate_flatten_eq {β : Type} (w : List β) :
    ∀ (s m : Nat), (List.replicate m w).flatten = (List.range' s m).flatMap (fun _ => w)
  | _, 0 => rfl
  | s, m+1 => by
      rw [List.replicate_succ, List.flatten_cons, List.range'_succ, List.flatMap_cons,
        replicate_flatten_eq w (s+1) m]

end TwoPermutationPrototype.ArtifactMatchB
