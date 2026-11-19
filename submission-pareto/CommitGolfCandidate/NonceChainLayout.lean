import CommitGolfCandidate.NonceChainGame
import CommitGolf.Parameters
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.FinEnum

/-! Eleven 128-bit nonces and a hidden 192-bit suffix fill one permutation reply.
Projection onto the first LENGTH nonce coordinates drops the unroll padding. -/
namespace CommitGolfCandidate.Permutation.NonceChain
open CommitGolf Finset
set_option exponentiation.threshold 2048
set_option maxRecDepth 8000

abbrev Word1600 := BitVec 1600
abbrev Key := BitVec 192
abbrev Nonce := BitVec 128
abbrev Block := Fin 11 → Nonce
abbrev blocks : Nat := 1525248
def blockParts (w : Word1600) : Block × Key :=
  (fun j => w.extractLsb' (128*j.val) 128, w.extractLsb' 1408 192)

private theorem parts_injective : Function.Injective blockParts := by
  intro a b eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases lo : i<1408
  · let j : Fin 11 := ⟨i/128,by omega⟩
    have bit := congrArg (fun p : Block × Key => (p.1 j).getLsbD (i%128)) eq
    change (a.extractLsb' (128*(i/128)) 128).getLsbD (i%128) =
      (b.extractLsb' (128*(i/128)) 128).getLsbD (i%128) at bit
    simpa only [BitVec.getLsbD_extractLsb', Nat.mod_lt i (by decide : 0<128),
      decide_true,Bool.true_and,Nat.div_add_mod] using bit
  · have bit := congrArg (fun p : Block × Key => p.2.getLsbD (i-1408)) eq
    change (a.extractLsb' 1408 192).getLsbD (i-1408) = (b.extractLsb' 1408 192).getLsbD (i-1408) at bit
    simpa only [BitVec.getLsbD_extractLsb',show i-1408<192 by omega,decide_true,
      Bool.true_and,show 1408+(i-1408)=i by omega] using bit

noncomputable def blockEquiv : Word1600 ≃ Block × Key :=
  Equiv.ofBijective blockParts ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨parts_injective,by
      change Fintype.card (BitVec 1600) = Fintype.card ((Fin 11 → BitVec 128) × BitVec 192)
      rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
      have card (n : ℕ) : Fintype.card (BitVec n) = 2^n := by
        rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
      rw [card,card,card]
      norm_num⟩)

def seedState (k : Key) : Word1600 := BitVec.ofNat 1600 k.toNat

theorem seed_injective : Function.Injective seedState := by
  intro k k' eq
  have h := congrArg BitVec.toNat eq
  have lt (x : Key) : x.toNat < 2^1600 := lt_trans x.isLt (by decide)
  exact BitVec.eq_of_toNat_eq (by simpa only [seedState,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (lt k),Nat.mod_eq_of_lt (lt k')] using h)

def nonceAt (p : Fin blocks → Block) (i : Fin LENGTH) : Nonce :=
  p ⟨i.val/11,by have := i.isLt;dsimp [blocks,LENGTH,LOG_LENGTH] at *;omega⟩
    ⟨i.val%11,Nat.mod_lt _ (by decide)⟩

noncomputable def actualNonces (π : Equiv.Perm Word1600) (k : Key) :=
  nonceAt (fun i => (blockEquiv (orbit π (seedState k) (i.val+1))).1)

/-- The rectangular tape is in bijection with the used array and its 512 spare coordinates. -/
def projectTape : (Fin blocks → Block) ≃ (Fin LENGTH → Nonce) × (Fin 512 → Nonce) where
  toFun p := (nonceAt p, fun i =>
    p ⟨(LENGTH+i.val)/11,by have := i.isLt; dsimp [blocks,LENGTH,LOG_LENGTH];omega⟩
      ⟨(LENGTH+i.val)%11,Nat.mod_lt _ (by decide)⟩)
  invFun t j k := if h : 11*j.val+k.val < LENGTH then t.1 ⟨_,h⟩
    else t.2 ⟨11*j.val+k.val-LENGTH,by
      have := j.isLt
      have := k.isLt
      dsimp [blocks,LENGTH,LOG_LENGTH] at *
      omega⟩
  left_inv p := by
    funext j k
    dsimp only
    split
    · unfold nonceAt
      apply congrArg₂ (fun j k => p j k) <;> apply Fin.ext <;> dsimp only <;> omega
    · apply congrArg₂ (fun j k => p j k) <;> apply Fin.ext <;> dsimp only <;> omega
  right_inv t := by
    apply Prod.ext <;> funext i
    · unfold nonceAt
      simp only [Nat.div_add_mod, i.isLt, ↓reduceDIte]
    · simp only [Nat.div_add_mod, Nat.not_lt_of_ge (Nat.le_add_right LENGTH i.val),
        ↓reduceDIte, Nat.add_sub_cancel_left]

theorem chain_budget (t : Nat) :
    let q := t + 2*LENGTH + t
    ((t : ℝ)+1)/2^121 +
      2 * (((blocks+1 : Nat) : ℝ) * ((2*q+(blocks+1) : ℝ)/2^192)) ≤
        ((t : ℝ)+1)/2^120 := by
  norm_num [blocks,LENGTH,LOG_LENGTH,Nat.cast_add,Nat.cast_mul]
  nlinarith [Nat.cast_nonneg (α := ℝ) t]

end CommitGolfCandidate.Permutation.NonceChain
