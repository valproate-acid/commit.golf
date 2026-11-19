import CommitGolfCandidate.QuadBindingProbability
import CommitGolfCandidate.TwoPermutationPackedPaths

/-! Deterministic binding extraction for penta openings. From the pinned leaf to
the root, each of the eleven levels is one recorded D5 row whose input carries
the current digest in slot `(i / 5^k) % 5`; the reply's low 256 bits are the
next digest, and the last one is the commitment. Siblings are unconstrained. -/
namespace TwoPermutationPrototype.Quad
open CommitGolf CommitGolf.Riscv CommitGolfCandidate
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Checker OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

private theorem append_parts {a b : Nat} {x x' : BitVec a} {y y' : BitVec b}
    (eq : x ++ y = x' ++ y') : x=x' ∧ y=y' := by
  constructor
  · have hit := congrArg (fun v : BitVec (a+b) => v.extractLsb' b a) eq
    exact BitVec.extractLsb'_append_eq_left.symm.trans (hit.trans BitVec.extractLsb'_append_eq_left)
  · have hit := congrArg (fun v : BitVec (a+b) => v.extractLsb' 0 b) eq
    exact BitVec.extractLsb'_append_eq_right.symm.trans (hit.trans BitVec.extractLsb'_append_eq_right)

/-- Slot extraction is injective; equal penta inputs force every child equal. -/
theorem penta_children_equal {c d : Fin 5 → BitVec 256} (same : pentaInput c = pentaInput d) : c=d := by
  have h := (append_parts same).1
  obtain ⟨h,h0⟩ := append_parts h
  obtain ⟨h,h1⟩ := append_parts h
  obtain ⟨h,h2⟩ := append_parts h
  obtain ⟨h4,h3⟩ := append_parts h
  funext k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- The slot of position `index` among the children of its level-`(k+1)` node. -/
def pentaSlot (index k : Nat) : Fin 5 := ⟨index / 5 ^ k % 5, Nat.mod_lt _ (by decide)⟩

/-- A recorded D5 path from level `k`, `left` levels up. -/
inductive PentaPath (rows : List PublicRow) (index : Nat) : Nat → Nat → BitVec 256 → BitVec 256 → Prop
  | done (k : Nat) (digest : BitVec 256) : PentaPath rows index k 0 digest digest
  | step (k left : Nat) (digest finish : BitVec 256) (children : Fin 5 → BitVec 256) (answer : Block)
      (opened : children (pentaSlot index k) = digest)
      (row : PublicRow.permutation (pentaInput children) answer ∈ rows)
      (rest : PentaPath rows index (k+1) left (answer.extractLsb' 0 256) finish) :
      PentaPath rows index k (left+1) digest finish

theorem PentaPath.mono {rows rows' : List PublicRow} {index k left : Nat} {d f : BitVec 256}
    (path : PentaPath rows index k left d f) (contained : ∀ row ∈ rows, row ∈ rows') :
    PentaPath rows' index k left d f := by
  induction path with
  | done k d => exact .done k d
  | step k left d f c a opened row rest ih => exact .step k left d f c a opened (contained _ row) ih

theorem PentaPath.append {rows : List PublicRow} {index k left more : Nat} {d m f : BitVec 256}
    (first : PentaPath rows index k left d m) (second : PentaPath rows index (k+left) more m f) :
    PentaPath rows index k (left+more) d f := by
  induction first with
  | done k d => simpa using second
  | step k left d m c a opened row rest ih =>
    rw [show left+1+more=(left+more)+1 by omega]
    exact .step k (left+more) d f c a opened row (ih (by simpa [Nat.add_assoc,Nat.add_comm 1 left] using second))

/-- Two paths to the same digest: a D5 collision or the same starting digest. -/
theorem PentaPath.compare {rows₀ rows₁ : List PublicRow} {index k left : Nat} {d₀ d₁ f : BitVec 256}
    (left₀ : PentaPath rows₀ index k left d₀ f) (right₀ : PentaPath rows₁ index k left d₁ f) :
    PentaWitness (rows₀++rows₁) ∨ d₀=d₁ := by
  induction left₀ generalizing d₁ with
  | done k d =>
    cases right₀
    exact Or.inr rfl
  | step k left d f c a opened row rest ih =>
    cases right₀ with
    | step _ _ _ _ c' a' opened' row' rest' =>
      rcases ih rest' with hit | sameOut
      · exact Or.inl hit
      · by_cases sameIn : pentaInput c = pentaInput c'
        · have children := penta_children_equal sameIn
          exact Or.inr (opened.symm.trans ((congrFun children _).trans opened'))
        · exact Or.inl ⟨_,_,a,a',List.mem_append_left _ row,List.mem_append_right _ row',
            fun eq => sameIn (congrArg pentaEncode eq),sameOut⟩

structure PentaOpening (oracle : Oracle) (index : Index) (entry : Entry) (root : Commitment)
    (rows : List PublicRow) : Prop where
  nonce : ∃ nonce : Words 2,
    PublicRow.permutation
      (pinnedFirstRow oracle.permutation (entryWords entry)).1
      (pinnedFirstRow oracle.permutation (entryWords entry)).2 ∈ rows ∧
    PublicRow.permutation
      (pinnedSecondRow oracle.permutation index nonce
        (pinnedFirstRow oracle.permutation (entryWords entry)).2 (entryWords entry)).1
      (pinnedSecondRow oracle.permutation index nonce
        (pinnedFirstRow oracle.permutation (entryWords entry)).2 (entryWords entry)).2 ∈ rows ∧
    PentaPath rows index.val 0 PENTA_LEVELS
      (outputDigest (pinnedSecondRow oracle.permutation index nonce
        (pinnedFirstRow oracle.permutation (entryWords entry)).2 (entryWords entry)).2) root

theorem PentaOpening.mono {oracle : Oracle} {index : Index} {entry : Entry} {root : Commitment}
    {earlier later : List PublicRow} (opening : PentaOpening oracle index entry root earlier)
    (contained : ∀ row ∈ earlier, row ∈ later) : PentaOpening oracle index entry root later := by
  obtain ⟨nonce,first,second,path⟩ := opening.nonce
  exact ⟨⟨nonce,contained _ first,contained _ second,path.mono contained⟩⟩

theorem penta_openings_conflict (oracle : Oracle) (index : Index) (root : Commitment)
    (value₀ value₁ : Entry) (conflict : value₀ ≠ value₁)
    (rows₀ rows₁ : List PublicRow) (left : PentaOpening oracle index value₀ root rows₀)
    (right : PentaOpening oracle index value₁ root rows₁) : PentaReplayEvidence (rows₀++rows₁) := by
  obtain ⟨n₀,first₀,second₀,path₀⟩ := left.nonce
  obtain ⟨n₁,first₁,second₁,path₁⟩ := right.nonce
  rcases path₀.compare path₁ with hit | sameLeaf
  · exact Or.inr hit
  · exact Or.inl ⟨oracle.permutation,index,n₀,n₁,entryWords value₀,entryWords value₁,
      List.mem_append_left _ first₀,List.mem_append_right _ first₁,
      List.mem_append_left _ second₀,List.mem_append_right _ second₁,
      sameLeaf,fun h => conflict (entry_words_injective h)⟩

def PentaAcceptedTrace (s : Submission) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput),
    let observed := checkObservation s oracle input
    observed.1.1.exit = .success → observed.2 ≤ 2^30 ∧
      ∀ index : {i // i ∈ input.positions},
        PentaOpening oracle index.val (input.values index) input.commitment observed.1.2

private theorem penta_limited_check (s : Submission) (oracle : Oracle) (input : CheckInput)
    (fits : (checkObservation s oracle input).2 ≤ 2^30) :
    fixedOracleRun oracle (recordRows (limitPublicQueries (s.run .check input) (2^30))) =
      pure (some (checkObservation s oracle input).1.1,(checkObservation s oracle input).1.2) := by
  have coinFree := check_public_only s input
  rw [(coinFree.limit (2^30)).record.fixed oracle,coinFree.limit_recorded oracle _ fits]
  rfl

theorem penta_replay_extracts (s : Submission) (refines : PentaAcceptedTrace s)
    (oracle : Oracle) (claim : Scheme.Claim) (breaks : s.scheme.Breaks oracle claim) :
    ∀ result ∈ support (fixedOracleRun oracle (recordRows (checkerReplay s claim))), PentaReplayEvidence result.2 := by
  obtain ⟨⟨index,member₀,member₁,conflict⟩,accepted₀,accepted₁⟩ := breaks
  let x := leftCheck claim
  let y := rightCheck claim
  have good₀ := checked_acceptance s oracle x accepted₀
  have good₁ := checked_acceptance s oracle y accepted₁
  obtain ⟨fits₀,path₀⟩ := refines oracle x good₀
  obtain ⟨fits₁,path₁⟩ := refines oracle y good₁
  have replay : fixedOracleRun oracle (recordRows (checkerReplay s claim)) =
      pure ((),(checkObservation s oracle x).1.2++(checkObservation s oracle y).1.2) := by
    unfold checkerReplay
    change fixedOracleRun oracle
      (recordRows (do
        let _ ← limitPublicQueries (s.run .check x) (2^30)
        let _ ← limitPublicQueries (s.run .check y) (2^30)
        pure ())) = _
    have tail : fixedOracleRun oracle
        (recordRows (do let _ ← limitPublicQueries (s.run .check y) (2^30); pure ())) =
        pure ((), (checkObservation s oracle y).1.2) := by
      rw [record_rows_bind, fixed_oracle_run_bind, penta_limited_check s oracle y fits₁]
      simp [record_rows_pure, fixed_oracle_run_pure, fixed_oracle_run_bind]
    rw [record_rows_bind, fixed_oracle_run_bind, penta_limited_check s oracle x fits₀]
    simp only [pure_bind]
    rw [fixed_oracle_run_bind, tail]
    simp [fixed_oracle_run_pure]
  rw [replay]
  intro result found
  simp only [support_pure,Set.mem_singleton_iff] at found
  subst result
  exact penta_openings_conflict oracle index claim.root _ _ conflict _ _
    (path₀ ⟨index,member₀⟩) (path₁ ⟨index,member₁⟩)

def penta_binding_replay (s : Submission) (specified : PentaAcceptedTrace s) :
    BindingReplayEvidence s.scheme PentaReplayEvidence :=
  ⟨checkerReplay s,checker_replay_bounded s,penta_replay_extracts s specified⟩

/-- The final all-budget Binding clause needs only the machine's accepted-trace
extraction theorem, and makes no assumption about commit or opening images. -/
theorem binding_of_penta_trace (candidate : Submission) (trace : PentaAcceptedTrace candidate) :
    candidate.scheme.Binding :=
  scheme_binding_of_replay_with candidate.scheme (penta_binding_replay candidate trace)
    (fun contained hit => hit.mono contained) penta_replay_bound

end TwoPermutationPrototype.Quad
