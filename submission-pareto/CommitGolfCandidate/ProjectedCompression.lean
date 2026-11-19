import CommitGolfCandidate.ProjectedCollisionROM
import CommitGolfCandidate.Model

/-! Internal tree nodes store a zero-extended 240-bit digest. -/
namespace CommitGolfCandidate.ShortTree
open CommitGolf

def padLow (x : Digest) : Digest := (0 : BitVec 16) ++ low240 x

def parentCompression (compress : Compression) : Compression := fun input => padLow (compress input)

theorem low240_padLow (digest : Digest) : low240 (padLow digest) = low240 digest :=
  BitVec.extractLsb'_append_eq_right (a := (0 : BitVec 16)) (b := low240 digest)

def parentOracle (oracle : Oracle) : Oracle :=
  { oracle with compression := parentCompression oracle.compression }

end CommitGolfCandidate.ShortTree
