import CommitGolfCandidate.CapMultiproof
import CommitGolfCandidate.Binding

/-! Authentication witnesses for arbitrary accepted cap transcripts. The relation
records the compression inputs of the recursive decoder; operational replay and
machine refinement remain separate obligations. -/
namespace CommitGolfCandidate
open CommitGolf

def capLeafValue : {height : Nat} → CapView height → Path height → Option Digest
  | _, .leaf known, .here => known
  | _, .node left _, .left path => capLeafValue left path
  | _, .node _ right, .right path => capLeafValue right path

/-- Bottom-up orientation bits, matching the existing collision extractor. -/
def capPathBits : {height : Nat} → Path height → List Bool
  | _, .here => []
  | _, .left path => capPathBits path ++ [false]
  | _, .right path => capPathBits path ++ [true]

theorem cap_leaf_occupied {height : Nat} (view : CapView height) (path : Path height)
    (value : Digest) (known : capLeafValue view path = some value) :
    capOccupied view = true := by
  induction view with
  | leaf leaf => cases path; simp [capLeafValue] at known; simp [capOccupied, known]
  | node left right ihLeft ihRight =>
      cases path with
      | left path => simp [capOccupied, ihLeft path known]
      | right path => simp [capOccupied, ihRight path known]

/-- An unknown subtree contributes its supplied root without a query. An expanded
node records its actual little-endian compression input after both child traces. -/
inductive CapDecodeWitness (compress : Compression) :
    {height : Nat} → CapView height → List Digest → Digest → List Digest →
      List (BitVec 512) → Prop where
  | unknown {height : Nat} (view : CapView height) (root : Digest) (rest : List Digest)
      (unoccupied : capOccupied view = false) :
      CapDecodeWitness compress view (root :: rest) root rest []
  | known (value : Digest) (proof : List Digest) :
      CapDecodeWitness compress (.leaf (some value)) proof value proof []
  | node {height : Nat} (left right : CapView height) (proof rest rest' : List Digest)
      (lroot rroot : Digest) (leftInputs rightInputs : List (BitVec 512))
      (occupied : capOccupied (.node left right) = true)
      (leftDecoded : CapDecodeWitness compress left proof lroot rest leftInputs)
      (rightDecoded : CapDecodeWitness compress right rest rroot rest' rightInputs) :
      CapDecodeWitness compress (.node left right) proof (combine compress lroot rroot)
        rest' (leftInputs ++ rightInputs ++ [rroot ++ lroot])

theorem cap_witness_decode (compress : Compression) {height : Nat}
    {view : CapView height} {proof rest : List Digest} {root : Digest}
    {inputs : List (BitVec 512)}
    (witness : CapDecodeWitness compress view proof root rest inputs) :
    capDecode compress view proof = some (root, rest) := by
  induction witness with
  | unknown view root rest unoccupied => cases view <;> simp [capDecode, unoccupied]
  | known value proof => rfl
  | node left right proof rest rest' lroot rroot leftInputs rightInputs occupied
      leftDecoded rightDecoded ihLeft ihRight =>
      simp only [capDecode, occupied, ↓reduceIte]
      rw [ihLeft]
      change (do
        let result ← capDecode compress right rest
        return (combine compress lroot result.1, result.2)) = _
      rw [ihRight]
      rfl

/-- Acceptance supplies a witness for arbitrary boundary digests, not only an
honest proof selected from a committed tree. -/
theorem cap_decode_witness (compress : Compression) {height : Nat}
    (view : CapView height) (proof rest : List Digest) (root : Digest)
    (accepted : capDecode compress view proof = some (root, rest)) :
    ∃ inputs, CapDecodeWitness compress view proof root rest inputs := by
  induction view generalizing proof rest root with
  | leaf known =>
      cases known with
      | none =>
          cases proof with
          | nil => simp [capDecode, capOccupied] at accepted
          | cons first suffix =>
              have pair : (first, suffix) = (root, rest) := by
                simpa [capDecode, capOccupied] using accepted
              cases pair
              exact ⟨[], .unknown (.leaf none) root rest rfl⟩
      | some value =>
          have pair : (value, proof) = (root, rest) := by
            simpa [capDecode, capOccupied] using accepted
          cases pair
          exact ⟨[], .known root proof⟩
  | node left right ihLeft ihRight =>
      by_cases occupied : capOccupied (.node left right) = true
      · simp only [capDecode, occupied, ↓reduceIte] at accepted
        cases leftResult : capDecode compress left proof with
        | none => simp [leftResult] at accepted
        | some pair =>
            rcases pair with ⟨lroot, suffix⟩
            simp only [leftResult] at accepted
            change (do
              let result ← capDecode compress right suffix
              return (combine compress lroot result.1, result.2)) = some (root, rest) at accepted
            cases rightResult : capDecode compress right suffix with
            | none => simp [rightResult] at accepted
            | some pair =>
                rcases pair with ⟨rroot, suffix'⟩
                have pair : (combine compress lroot rroot, suffix') = (root, rest) := by
                  simpa [rightResult] using accepted
                cases pair
                obtain ⟨leftInputs, leftWitness⟩ := ihLeft proof suffix lroot leftResult
                obtain ⟨rightInputs, rightWitness⟩ := ihRight suffix rest rroot rightResult
                exact ⟨_, .node left right proof suffix rest lroot rroot leftInputs
                  rightInputs occupied leftWitness rightWitness⟩
      · have unoccupied : capOccupied (.node left right) = false := by
          cases h : capOccupied (.node left right) <;> simp_all
        cases proof with
        | nil => simp [capDecode, unoccupied] at accepted
        | cons first suffix =>
            have pair : (first, suffix) = (root, rest) := by
              simpa [capDecode, unoccupied] using accepted
            cases pair
            exact ⟨[], .unknown (.node left right) root rest unoccupied⟩

theorem cap_path_inputs_append (compress : Compression) (value : Digest)
    (initial suffix : List (Bool × Digest)) :
    pathInputs compress value (initial ++ suffix) =
      pathInputs compress value initial ++ pathInputs compress (climb compress value initial) suffix := by
  induction initial generalizing value with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨right, sibling⟩
      cases right with
      | false => simpa [pathInputs, climb, combine] using ih (compress (sibling ++ value))
      | true => simpa [pathInputs, climb, combine] using ih (compress (value ++ sibling))

/-- Every known leaf of an accepted recursive witness has a path to its root.
All path compression inputs belong to that witness's recorded query trace. -/
theorem cap_witness_path (compress : Compression) {height : Nat}
    {view : CapView height} {proof rest : List Digest} {root : Digest}
    {inputs : List (BitVec 512)}
    (witness : CapDecodeWitness compress view proof root rest inputs)
    (path : Path height) (value : Digest) (known : capLeafValue view path = some value) :
    ∃ siblings : List (Bool × Digest), siblings.length = height ∧
      siblings.map Prod.fst = capPathBits path ∧
      climb compress value siblings = root ∧
      ∀ input ∈ pathInputs compress value siblings, input ∈ inputs := by
  induction witness with
  | unknown view root rest unoccupied =>
      have occupied := cap_leaf_occupied view path value known
      simp [unoccupied] at occupied
  | known leaf proof =>
      cases path
      simp only [capLeafValue, Option.some.injEq] at known
      subst value
      exact ⟨[], rfl, rfl, rfl, by simp [pathInputs]⟩
  | @node height left right proof rest rest' lroot rroot leftInputs rightInputs occupied
      leftDecoded rightDecoded ihLeft ihRight =>
      cases path with
      | left path =>
          obtain ⟨siblings, length, bits, rootEq, included⟩ := ihLeft path known
          refine ⟨siblings ++ [(false, rroot)], by simp [length],
            by simp [bits, capPathBits], ?_, ?_⟩
          · simp only [climb, List.foldl_append, List.foldl_cons, List.foldl_nil]
            change combine compress (climb compress value siblings) rroot = _
            rw [rootEq]
          · intro input member
            rw [cap_path_inputs_append] at member
            simp only [List.mem_append] at member
            rcases member with member | member
            · exact List.mem_append_left _ (List.mem_append_left _ (included input member))
            · apply List.mem_append_right
              simpa [pathInputs, rootEq] using member
      | right path =>
          obtain ⟨siblings, length, bits, rootEq, included⟩ := ihRight path known
          refine ⟨siblings ++ [(true, lroot)], by simp [length],
            by simp [bits, capPathBits], ?_, ?_⟩
          · simp only [climb, List.foldl_append, List.foldl_cons, List.foldl_nil]
            change combine compress lroot (climb compress value siblings) = _
            rw [rootEq]
          · intro input member
            rw [cap_path_inputs_append] at member
            simp only [List.mem_append] at member
            rcases member with member | member
            · exact List.mem_append_left _ (List.mem_append_right _ (included input member))
            · apply List.mem_append_right
              simpa [pathInputs, rootEq] using member
end CommitGolfCandidate
