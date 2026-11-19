import CommitGolf.Oracle

/-! Stage-3 leaf hash, pinned variant: two calls of the 1600-bit permutation.
`W1 = v[0..200)`, `o1 = P(W1)`, `W2 = r[0..24) || o1[112..200) || v[168..256)`,
digest = low 32 bytes of `P(W2)`. The 32 leaf bytes `v[168..200)` occur in both windows:
they pin the first window inside the second, which replaces the zero prefix of the
earlier layout. Bytes are little-endian as in the machine's buffers. -/
namespace CommitGolfCandidate
open CommitGolf

/-- First window: leaf bytes 0..200. -/
def s3First (value : Entry) : BitVec PERMUTATION_WIDTH :=
  BitVec.ofNat PERMUTATION_WIDTH (value.toNat % 2 ^ 1600)

/-- Second window: 24 nonce bytes, bytes 112..200 of the first reply, leaf bytes 168..256. -/
def s3Second (salt : BitVec 256) (reply : BitVec PERMUTATION_WIDTH) (value : Entry) :
    BitVec PERMUTATION_WIDTH :=
  BitVec.ofNat PERMUTATION_WIDTH
    (salt.toNat % 2 ^ 192 + (reply.toNat / 2 ^ 896) * 2 ^ 192 + (value.toNat / 2 ^ 1344) * 2 ^ 896)

/-- The stage-3 leaf digest: low 32 bytes of the second reply. -/
def s3LeafDigest (permutation : Perm) (salt : BitVec 256) (value : Entry) : BitVec 256 :=
  BitVec.ofNat 256 (permutation (s3Second salt (permutation (s3First value)) value)).toNat

end CommitGolfCandidate
