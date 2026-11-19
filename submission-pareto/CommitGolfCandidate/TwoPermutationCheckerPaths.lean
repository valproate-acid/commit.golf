import CommitGolfCandidate.TwoPermutationBindingBridge

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.RV64

/-- Heap order puts the left child in the low 256 bits of the compression input. -/
def pathPair (node : Nat) (child sibling : BitVec 256) : BitVec 512 :=
  if node % 2 = 0 then sibling ++ child else child ++ sibling

private theorem equal_path_pair {node : Nat} {child₀ sibling₀ child₁ sibling₁ : BitVec 256}
    (same : pathPair node child₀ sibling₀ = pathPair node child₁ sibling₁) : child₀ = child₁ := by
  by_cases parity : node % 2 = 0
  · simp only [pathPair, ite_eq_left parity] at same
    have hit := congrArg (fun packed : BitVec 512 => packed.extractLsb' 0 256) same
    exact BitVec.extractLsb'_append_eq_right.symm.trans (hit.trans BitVec.extractLsb'_append_eq_right)
  · simp only [pathPair, ite_eq_right parity] at same
    have hit := congrArg (fun packed : BitVec 512 => packed.extractLsb' 256 256) same
    exact BitVec.extractLsb'_append_eq_left.symm.trans (hit.trans BitVec.extractLsb'_append_eq_left)

/-- A proof path only cites compression rows actually recorded during the check. -/
inductive RecordedPath (rows : List PublicRow) : Nat → Nat → BitVec 256 → BitVec 256 → Prop where
  | done (node : Nat) (digest : BitVec 256) : RecordedPath rows node 0 digest digest
  | step {node height : Nat} {child parent sibling root : BitVec 256}
      (call : PublicRow.compression (pathPair node child sibling) parent ∈ rows)
      (next : RecordedPath rows (node / 2) height parent root) :
      RecordedPath rows node (height + 1) child root

theorem RecordedPath.mono {first last : List PublicRow} {node height : Nat}
    {start finish : BitVec 256} (path : RecordedPath first node height start finish)
    (contained : ∀ row ∈ first, row ∈ last) : RecordedPath last node height start finish := by
  induction path with
  | done node digest => exact .done node digest
  | step call _ ih => exact .step (contained _ call) ih

theorem RecordedPath.append {rows : List PublicRow} {node m n : Nat} {start middle finish : BitVec 256}
    (first : RecordedPath rows node m start middle)
    (last : RecordedPath rows (node / 2 ^ m) n middle finish) :
    RecordedPath rows node (m + n) start finish := by
  induction first with
  | done node digest =>
    simpa using last
  | @step node height child parent sibling root call next ih =>
    have address : node / 2 ^ (height + 1) = (node / 2) / 2 ^ height := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2]
    rw [address] at last
    rw [show height + 1 + n = (height + n) + 1 by omega]
    exact .step call (ih last)

/-- Two accepted paths for the same leaf either have equal leaf digests or
expose a collision in the recorded compression rows. -/
theorem RecordedPath.compare {rows : List PublicRow} {node height : Nat}
    {start₀ start₁ root : BitVec 256}
    (left : RecordedPath rows node height start₀ root)
    (right : RecordedPath rows node height start₁ root) :
    CompressionWitness rows ∨ start₀ = start₁ := by
  induction height generalizing node start₀ start₁ root with
  | zero =>
    cases left
    cases right
    exact Or.inr rfl
  | succ height ih =>
    cases left with
    | @step _ _ _ parent₀ sibling₀ _ call₀ tail₀ =>
      cases right with
      | @step _ _ _ parent₁ sibling₁ _ call₁ tail₁ =>
        rcases ih tail₀ tail₁ with collision | sameParent
        · exact Or.inl collision
        by_cases sameInput : pathPair node start₀ sibling₀ = pathPair node start₁ sibling₁
        · exact Or.inr (equal_path_pair sameInput)
        · exact Or.inl ⟨_, _, _, _, call₀, call₁, sameInput, congrArg low240 sameParent⟩

def entryWords (entry : Entry) : Words 32 := fun i => entry.extractLsb' (64*i.val) 64

theorem entry_words_injective : Function.Injective entryWords := by
  intro a b same
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  have bound : bit < 2048 := inside
  have offset : bit % 64 < 64 := by omega
  let word : Fin 32 := ⟨bit/64, by omega⟩
  have eq := congrArg (fun chunk : BitVec 64 => chunk.getLsbD (bit % 64)) (congrFun same word)
  have cover : 64 * (bit / 64) + bit % 64 = bit := by omega
  simpa [entryWords, word, offset, cover, Nat.add_comm] using eq

/-- The two forward permutation rows and the subsequent authenticated path for
an opened index, all in a single genuine checker replay. -/
structure RecordedOpening (oracle : Oracle) (index : Index) (entry : Entry) (root : Commitment)
    (rows : List PublicRow) where
  nonce : Words 2
  first : PublicRow.permutation
    (firstRow oracle.permutation index nonce (entryWords entry)).1
    (firstRow oracle.permutation index nonce (entryWords entry)).2 ∈ rows
  second : PublicRow.permutation
    (secondRow oracle.permutation index (entryWords entry)
      (firstRow oracle.permutation index nonce (entryWords entry)).2).1
    (secondRow oracle.permutation index (entryWords entry)
      (firstRow oracle.permutation index nonce (entryWords entry)).2).2 ∈ rows
  path : RecordedPath rows (LENGTH + index.val) LOG_LENGTH
    (outputDigest (secondRow oracle.permutation index (entryWords entry)
      (firstRow oracle.permutation index nonce (entryWords entry)).2).2) root

theorem recorded_openings_conflict (oracle : Oracle) (index : Index) (root : Commitment)
    (value₀ value₁ : Entry) (conflict : value₀ ≠ value₁)
    (rows₀ rows₁ : List PublicRow) (left : RecordedOpening oracle index value₀ root rows₀)
    (right : RecordedOpening oracle index value₁ root rows₁) :
    ReplayEvidence (rows₀ ++ rows₁) := by
  rcases (left.path.mono (fun _ h => List.mem_append_left _ h)).compare
    (right.path.mono (fun _ h => List.mem_append_right _ h)) with hash | sameLeaf
  · exact Or.inl hash
  · exact Or.inr ⟨oracle.permutation, index, left.nonce, right.nonce, entryWords value₀, entryWords value₁,
      List.mem_append_left _ left.first, List.mem_append_right _ right.first,
      List.mem_append_left _ left.second, List.mem_append_right _ right.second,
      sameLeaf, fun same => conflict (entry_words_injective same)⟩

end TwoPermutationPrototype.Sampling
