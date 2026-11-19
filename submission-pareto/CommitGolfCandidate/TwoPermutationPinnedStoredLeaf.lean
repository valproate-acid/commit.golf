import CommitGolfCandidate.TwoPermutationPinnedRecorded
import CommitGolfCandidate.TwoPermutationCheckerPaths

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation TwoPermutationPrototype.RV64
set_option maxRecDepth 8192

structure PeerLeafLayout where
  salt : Index → BitVec 128 → BitVec 256
  first : ∀ (index : Index) (value : CommitGolf.Entry),
    packBuffer (pinnedFirstInput (entryWords value)) = s3First value
  second : ∀ (index : Index) (value : CommitGolf.Entry) (nonce : BitVec 128) (reply : Block),
    packBuffer (pinnedSecondInput index (saltWords nonce) (replyWords reply) (entryWords value)) =
      s3Second (salt index nonce) reply value

private theorem trunc_digest (reply : Block) :
    s3PinCall.trunc reply = outputDigest reply := by
  change BitVec.ofNat 256 reply.toNat = reply.extractLsb' 0 256
  apply BitVec.eq_of_toNat_eq
  simp [outputDigest,BitVec.extractLsb',BitVec.toNat_setWidth]

private theorem stored_evaluation (layout : PeerLeafLayout) (t : Trace PermState) (rows : List PublicRow)
    (stored : PinnedRowsStored rows t) (perm : Block → Block) (i : Index)
    (salt : BitVec 128) (value : CommitGolf.Entry)
    (ha : let a := pinnedFirstRow perm (entryWords value); PublicRow.permutation a.1 a.2 ∈ rows)
    (hb : let a := pinnedFirstRow perm (entryWords value)
          let b := pinnedSecondRow perm i (saltWords salt) a.2 (entryWords value)
          PublicRow.permutation b.1 b.2 ∈ rows) :
    let a := pinnedFirstRow perm (entryWords value)
    let b := pinnedSecondRow perm i (saltWords salt) a.2 (entryWords value)
    s3PinCall.Evaluates t (s3Input (layout.salt i salt,value)) (outputDigest b.2) := by
  let leaf := (layout.salt i salt,value)
  let a := pinnedFirstRow perm (entryWords value)
  let b := pinnedSecondRow perm i (saltWords salt) a.2 (entryWords value)
  obtain ⟨e,he,ein,eout⟩ := stored a.1 a.2 ha
  obtain ⟨f,hf,fin,fout⟩ := stored b.1 b.2 hb
  have first : e.inp = s3PinCall.enc1 (s3Input leaf).1 :=
    ein.trans ((layout.first i value).trans (s3_first_eq leaf))
  refine ⟨e,he,f,hf,first,?_,?_⟩
  · rw [eout,first]
    exact fin.trans ((layout.second i value salt a.2).trans (s3_second_eq leaf a.2))
  · exact (congrArg s3PinCall.trunc fout).trans (trunc_digest b.2)

theorem pinned_witness_bad (layout : PeerLeafLayout) (t : Trace PermState) (rows : List PublicRow) (stored : PinnedRowsStored rows t)
    (hit : PinnedLeafWitness rows) : ¬ s3PinCall.badSpec.Good t := by
  obtain ⟨perm,i,n,m,v,w,a₀,a₁,b₀,b₁,digest,conflict⟩ := hit
  obtain ⟨salt₀,hs₀⟩ := (split_blocks_bijective 64 2 (by decide)).2 n
  obtain ⟨salt₁,hs₁⟩ := (split_blocks_bijective 64 2 (by decide)).2 m
  obtain ⟨value₀,hv₀⟩ := (split_blocks_bijective 64 32 (by decide)).2 v
  obtain ⟨value₁,hv₁⟩ := (split_blocks_bijective 64 32 (by decide)).2 w
  change saltWords salt₀=n at hs₀
  change saltWords salt₁=m at hs₁
  change entryWords value₀=v at hv₀
  change entryWords value₁=w at hv₁
  subst n m v w
  have distinct : value₀ ≠ value₁ := fun h => conflict (congrArg entryWords h)
  have left := stored_evaluation layout t rows stored perm i salt₀ value₀ a₀ b₀
  have right := stored_evaluation layout t rows stored perm i salt₁ value₁ a₁ b₁
  refine s3PinCall.collision_imp_bad (s3_input_ne (leaf := (layout.salt i salt₀,value₀))
    (leaf' := (layout.salt i salt₁,value₁)) distinct) left ?_
  exact digest.symm ▸ right

end TwoPermutationPrototype.Sampling
