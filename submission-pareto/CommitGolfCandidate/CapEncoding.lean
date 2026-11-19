import CommitGolfCandidate.CapLowerParser

/-! Header-free byte encoding of lower records and the canonical cap frontier.
These are semantic byte counts. The machine still must be proved to emit these
exact bytes before this bound can enter an image certificate. -/
namespace CommitGolfCandidate
open CommitGolf

def capDigestEncoding (digests : List Digest) : Proof :=
  digests.flatMap digestBytes

theorem cap_digest_encoding_length (digests : List Digest) :
    (capDigestEncoding digests).length = 32 * digests.length := by
  induction digests with
  | nil => rfl
  | cons digest rest ih =>
      simp only [capDigestEncoding, List.flatMap_cons, List.length_append,
        digestBytes_length] at ih ⊢
      simp only [List.length_cons]
      omega

theorem cap_lower_encoding_length (record : CapLowerRecord) :
    (capLowerEncoding record).length = 17 := by
  simp [capLowerEncoding]

theorem cap_lower_transcript_length (records : List CapLowerRecord) :
    (capLowerTranscript records).length = 17 * records.length := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      simp only [capLowerTranscript, List.flatMap_cons, List.length_append,
        cap_lower_encoding_length] at ih ⊢
      simp only [List.length_cons]
      omega

/-- Empty positions produce no cap frontier, even though the standalone unknown
cap decoder would otherwise consume one root digest. -/
def capHonestBytes (compress : Compression) (records : List CapLowerRecord)
    (tree : Tree 8) (view : CapView 8) : Proof :=
  if records.length = 0 then []
  else capDigestEncoding (capLowerTranscript records ++ capProof compress tree view)

theorem cap_honest_bytes_length (compress : Compression) (records : List CapLowerRecord)
    (tree : Tree 8) (view : CapView 8) (nonempty : records ≠ []) :
    (capHonestBytes compress records tree view).length =
      544 * records.length + 32 * (capProof compress tree view).length := by
  rw [capHonestBytes, if_neg (by simpa using nonempty), cap_digest_encoding_length, List.length_append,
    cap_lower_transcript_length]
  omega

/-- A batch of 128 lower records uses 69,632 bytes; the occupied height-eight
frontier contributes at most another 4,096 bytes, with no headers. -/
theorem cap_honest_bytes_batch_bound (compress : Compression)
    (records : List CapLowerRecord) (tree : Tree 8) (view : CapView 8)
    (batch : records.length = BATCH) (occupied : capOccupied view = true) :
    (capHonestBytes compress records tree view).length ≤ 73728 := by
  have nonempty : records ≠ [] := by
    intro empty
    rw [empty] at batch
    change 0 = 128 at batch
    contradiction
  rw [cap_honest_bytes_length _ _ _ _ nonempty, batch]
  have boundary := cap_occupied_proof_bound compress tree view occupied
  change 544 * 128 + 32 * (capProof compress tree view).length ≤ 73728
  omega

theorem cap_honest_bytes_empty (compress : Compression) (tree : Tree 8) (view : CapView 8) :
    capHonestBytes compress [] tree view = [] := by
  simp [capHonestBytes]
end CommitGolfCandidate
