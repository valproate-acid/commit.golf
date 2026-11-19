import CommitGolfCandidate.S3PermPinCall
import Mathlib.Data.FinEnum

/-!
# The stage-3 byte layout as a pinned two-call hash, with its counts

`s3PinCall` is the `PinCall` instance on the 1600-bit state behind `s3First`, `s3Second` and
`s3LeafDigest` (S3Leaf.lean, pinned layout; the link is proved in S3LeafBinding.lean):

* first-call input `x1`: leaf bytes 0..200 (1600 bits), the whole first window;
* pinned part of a first-call input: its bytes 168..200 (256 bits);
* chaining value: bytes 112..200 of a reply (704 bits);
* second-call input: nonce (192 bits), chaining value, pinned part, leaf bytes 200..256
  (448 bits);
* digest: bytes 0..32 of a reply.

Counts: `2^1344` states per digest, `2^896` states per chaining value, `2^1344` states per pinned
part, `2^896` second-call inputs per chaining slot. A fresh forward answer is bad for at most
`2^1344 + 2 · 2^896` values, a fresh inverse answer for at most `2^896 + 2 · 2^1344`, so
`2^1345 + 2^897` bounds both; the unary event has at most `2^896` bad answers.
`s3_union_bound_le` reads the union bound at these sizes: for `q` adversary queries and `e`
probed leaves with `q + 2 e ≤ 2^128`, it is at most `(q + 2 e)^2 / 2^256 + q / 2^127`. This file
needs Mathlib only.
-/

set_option exponentiation.threshold 2100

namespace CommitGolfCandidate.Permutation

open Finset

/-- The state of the ideal permutation. -/
abbrev S3State := BitVec 1600

/-- Input of the pinned two-call leaf hash: leaf bytes 0..200, nonce, leaf bytes 200..256. -/
abbrev S3LeafInput := BitVec 1600 × BitVec 192 × BitVec 448

theorem s3_card_bitvec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

theorem s3_card_state : Fintype.card S3State = 2 ^ 1600 := s3_card_bitvec _

theorem s3_state_lt (s : S3State) : s.toNat < 2 ^ 1600 := s.isLt

theorem s3_enc1_injective :
    Function.Injective fun x : BitVec 1600 => (BitVec.ofNat 1600 x.toNat : S3State) := by
  intro x y h
  have hx := x.isLt
  have hy := y.isLt
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h'
  apply BitVec.eq_of_toNat_eq
  omega

theorem s3_enc2_injective :
    Function.Injective fun i : BitVec 192 × BitVec 704 × BitVec 256 × BitVec 448 =>
      (BitVec.ofNat 1600 (i.1.toNat + i.2.1.toNat * 2 ^ 192 + i.2.2.1.toNat * 2 ^ 896 +
        i.2.2.2.toNat * 2 ^ 1152) : S3State) := by
  rintro ⟨r, c, p, m⟩ ⟨r', c', p', m'⟩ h
  have hr := r.isLt
  have hc := c.isLt
  have hp := p.isLt
  have hm := m.isLt
  have hr' := r'.isLt
  have hc' := c'.isLt
  have hp' := p'.isLt
  have hm' := m'.isLt
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h'
  have e1 : r.toNat = r'.toNat := by omega
  have e2 : c.toNat = c'.toNat := by omega
  have e3 : p.toNat = p'.toNat := by omega
  have e4 : m.toNat = m'.toNat := by omega
  rw [BitVec.eq_of_toNat_eq e1, BitVec.eq_of_toNat_eq e2, BitVec.eq_of_toNat_eq e3,
    BitVec.eq_of_toNat_eq e4]

/-- The stage-3 leaf hash as a pinned two-call hash on the 1600-bit state. A leaf input is
`(first window, nonce, last 56 leaf bytes)`; the second call encodes
`(nonce, chaining value, pinned part of the first window, last 56 leaf bytes)`. -/
def s3PinCall : PinCall S3State (BitVec 1600) (BitVec 192) (BitVec 704) (BitVec 256)
    (BitVec 448) (BitVec 256) where
  enc1 x := BitVec.ofNat 1600 x.toNat
  pin s := BitVec.ofNat 256 (s.toNat / 2 ^ 1344)
  chop o := BitVec.ofNat 704 (o.toNat / 2 ^ 896)
  enc2 i := BitVec.ofNat 1600 (i.1.toNat + i.2.1.toNat * 2 ^ 192 + i.2.2.1.toNat * 2 ^ 896 +
    i.2.2.2.toNat * 2 ^ 1152)
  trunc o := BitVec.ofNat 256 o.toNat
  enc1_inj := s3_enc1_injective
  enc2_inj := s3_enc2_injective

/-! ### Counts -/

theorem s3_second_inputs :
    Fintype.card (BitVec 192) * Fintype.card (BitVec 256) * Fintype.card (BitVec 448) ≤
      2 ^ 896 := by
  rw [s3_card_bitvec, s3_card_bitvec, s3_card_bitvec, ← pow_add, ← pow_add]

/-- At most `2^896` states have a given chaining value. -/
theorem s3_chop_fiber (c : BitVec 704) :
    (univ.filter fun s : S3State => s3PinCall.chop s = c).card ≤ 2 ^ 896 := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun s : S3State => s3PinCall.chop s = c)
    (t := (univ : Finset (BitVec 896))) (fun s => BitVec.ofNat 896 s.toNat)
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [s3PinCall, BitVec.toNat_ofNat] at e1 e2
      have hA := s3_state_lt a
      have hB := s3_state_lt b
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s3_card_bitvec] at h

/-- At most `2^1344` states have a given pinned part. -/
theorem s3_pin_fiber (p : BitVec 256) :
    (univ.filter fun s : S3State => s3PinCall.pin s = p).card ≤ 2 ^ 1344 := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun s : S3State => s3PinCall.pin s = p)
    (t := (univ : Finset (BitVec 1344))) (fun s => BitVec.ofNat 1344 s.toNat)
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [s3PinCall, BitVec.toNat_ofNat] at e1 e2
      have hA := s3_state_lt a
      have hB := s3_state_lt b
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s3_card_bitvec] at h

/-- At most `2^1344` states have a given digest. -/
theorem s3_trunc_fiber (d : BitVec 256) :
    (univ.filter fun s : S3State => s3PinCall.trunc s = d).card ≤ 2 ^ 1344 := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun s : S3State => s3PinCall.trunc s = d)
    (t := (univ : Finset (BitVec 1344))) (fun s => BitVec.ofNat 1344 (s.toNat / 2 ^ 256))
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [s3PinCall, BitVec.toNat_ofNat] at e1 e2
      have hA := s3_state_lt a
      have hB := s3_state_lt b
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s3_card_bitvec] at h

/-! ### The union bound at these sizes -/

/-- Real-number core: with `N = a 2^256` states, `2a + 2b` bad answers per older entry and `b`
unary bad answers, where `2^128 b < a`, and `Q ≤ 2^128` queries of which `q` may be inverse.
The `- Q k / 2` part of `Q (Q - 1) / 2 · k` pays for the excess of `k / N` over `2^-255`. -/
theorem s3_union_core (a b Q q : ℝ) (hb : 0 ≤ b) (hab : 2 ^ 128 * b + 1 ≤ a) (hQ0 : 0 ≤ Q)
    (hQ : Q ≤ 2 ^ 128) (hq0 : 0 ≤ q) :
    (Q * (Q - 1) / 2 * (2 * a + 2 * b) + q * b) / (a * 2 ^ 256 - Q) ≤
      Q ^ 2 / 2 ^ 256 + q / 2 ^ 127 := by
  have h128 : (0 : ℝ) ≤ 2 ^ 128 * b := by positivity
  have ha : 1 ≤ a := by linarith
  have hDpos : 0 < a * 2 ^ 256 - Q := by
    have h1 : (2 : ℝ) ^ 256 ≤ a * 2 ^ 256 := by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) 256]
    have h2 : (2 : ℝ) ^ 128 < 2 ^ 256 := by norm_num
    linarith
  rw [div_le_iff₀ hDpos]
  have hid : (Q ^ 2 / 2 ^ 256 + q / 2 ^ 127) * (a * 2 ^ 256 - Q) -
      (Q * (Q - 1) / 2 * (2 * a + 2 * b) + q * b) =
      Q * (a + b - Q * b - Q ^ 2 / 2 ^ 256) + q * (2 ^ 129 * a - b - Q / 2 ^ 127) := by
    ring
  have hQb : Q * b ≤ 2 ^ 128 * b := mul_le_mul_of_nonneg_right hQ hb
  have hQ2 : Q ^ 2 / 2 ^ 256 ≤ 1 := by
    rw [div_le_one (by positivity)]
    calc Q ^ 2 ≤ (2 ^ 128) ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
      _ = 2 ^ 256 := by norm_num
  have hQ127 : Q / 2 ^ 127 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (2 : ℝ) * 2 ^ 127 = 2 ^ 128 := by norm_num
    linarith
  have k1 : 0 ≤ a + b - Q * b - Q ^ 2 / 2 ^ 256 := by linarith
  have k2 : 0 ≤ 2 ^ 129 * a - b - Q / 2 ^ 127 := by
    have h3 : (2 : ℝ) ^ 129 = 2 * 2 ^ 128 := by norm_num
    have h4 : b ≤ 2 ^ 128 * b := by
      have : (1 : ℝ) ≤ 2 ^ 128 := by norm_num
      nlinarith
    nlinarith
  have := mul_nonneg hQ0 k1
  have := mul_nonneg hq0 k2
  linarith

/-- **The union bound at the stage-3 sizes.** `q` adversary queries (forward or inverse) and `e`
probed leaves (two forward queries each), with `q + 2 e ≤ 2^128`. -/
theorem s3_union_bound_le (q e : ℕ) (hsmall : q + 2 * e ≤ 2 ^ 128) :
    (((q + 2 * e : ℕ) : ℝ) * (((q + 2 * e : ℕ) : ℝ) - 1) / 2 *
        ((2 ^ 1345 + 2 ^ 897 : ℕ) : ℝ) + (q : ℝ) * ((2 ^ 896 : ℕ) : ℝ)) /
      ((Fintype.card S3State : ℝ) - ((q + 2 * e : ℕ) : ℝ)) ≤
      ((q : ℝ) + 2 * e) ^ 2 / 2 ^ 256 + (q : ℝ) / 2 ^ 127 := by
  have hcore := s3_union_core ((2 : ℝ) ^ 1344) ((2 : ℝ) ^ 896) ((q + 2 * e : ℕ) : ℝ) (q : ℝ)
    (by positivity) (by norm_num) (Nat.cast_nonneg _) (by exact_mod_cast hsmall)
    (Nat.cast_nonneg _)
  have hN : (Fintype.card S3State : ℝ) = (2 : ℝ) ^ 1344 * 2 ^ 256 := by
    rw [s3_card_state, ← pow_add]
    norm_num
  have hk : ((2 ^ 1345 + 2 ^ 897 : ℕ) : ℝ) = 2 * (2 : ℝ) ^ 1344 + 2 * 2 ^ 896 := by
    push_cast
    ring
  have hu : ((2 ^ 896 : ℕ) : ℝ) = (2 : ℝ) ^ 896 := by push_cast; ring
  rw [hN, hk, hu]
  have hcast : ((q + 2 * e : ℕ) : ℝ) = (q : ℝ) + 2 * e := by push_cast; ring
  rw [hcast] at hcore ⊢
  exact hcore

end CommitGolfCandidate.Permutation
