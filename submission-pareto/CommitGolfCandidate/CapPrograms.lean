import CommitGolfCandidate.Programs

/-! Height-eight cap opening/check assembly with packed 192-bit nonces.
CapCertificate assembles the complete machine and security certificate;
commitment code is supplied by the reference candidate. -/
namespace CommitGolfCandidate
open CommitGolf

def capHeight (depth : Nat) : Nat := min depth 8
def capLowerHeight (depth : Nat) : Nat := depth - capHeight depth

def capAndOne (destination source : Nat) : Asm :=
  insn (1*2^20 + source*2^15 + 7*2^12 + destination*2^7 + 0x13)

/-- x20 visits internal mark nodes in descending order; x6/x7/x23/x30 are scratch. -/
def capMarkParents (marks leafCount : Nat) : List Asm :=
  [addi 20 leafCount (-1), .branch 0 20 0 "cap-marks-done", .label "cap-marks",
   shift 30 20 4, regop 30 marks 30, ld 6 30 0, ld 7 30 8, regop 6 6 7 6,
   shift 23 20 3, regop 23 marks 23, sd 6 23 0,
   addi 20 20 (-1), .branch 1 20 0 "cap-marks", .label "cap-marks-done"]

/-- Iterative canonical DFS requires no stack. On returning from a right child,
checker compresses its parent's adjacent root slots before continuing upward.
Opening emits one trapdoor heap root for each unknown subtree. -/
def capWalk (checking : Bool) (marks leafCount roots proofEnd : Nat) : List Asm :=
  [addi 20 0 1, addi 31 0 1, .label "cap-visit",
   shift 7 20 3, regop 23 marks 7, ld 6 23 0,
   .branch 0 6 0 "cap-unknown", .branch 7 20 leafCount "cap-advance",
   shift 20 20 1, .jump 0 "cap-visit", addi 0 0 0, .label "cap-unknown"] ++
  (if checking then
    [addi 6 25 32, .branch 6 proofEnd 6 "reject",
     shift 7 20 5, regop 23 roots 7] ++ copyDigest 25 23
   else [shift 7 20 5, regop 23 roots 7] ++ copyDigest 23 25) ++
  [addi 25 25 32, .label "cap-advance", .branch 0 20 31 "cap-done",
   capAndOne 7 20, .branch 0 7 0 "cap-right", shift 20 20 1 true] ++
  (if checking then
    [shift 10 20 6, regop 10 roots 10, shift 12 20 5, regop 12 roots 12, insn 0x73]
   else []) ++
  [.jump 0 "cap-advance", .label "cap-right", addi 20 20 1, .jump 0 "cap-visit",
   .label "cap-done"]

def capOpeningCode (depth : Nat) : List Asm :=
  let lower := capLowerHeight depth
  let leaves := 2^depth
  let capLeaves := 2^(capHeight depth)
  [mv 9 12, mv 24 13, mv 25 15, mv 27 16] ++
  li 19 leaves ++ li 6 (64*leaves) ++ [regop 18 9 6] ++
  li 22 28672 ++ [addi 29 0 capLeaves, addi 17 0 24, addi 0 0 0] ++ [addi 31 0 1, .branch 0 27 0 "open-done",
   .label "open-position", ld 20 24 0, regop 6 20 17 0 1, regop 23 18 6] ++
  (copyDigest 23 25).take 6 ++ [sd 0 25 24, addi 0 0 0] ++
  [addi 25 25 32, regop 20 20 19] ++ li 28 lower ++
  [.branch 0 28 0 "open-group", .label "open-path",
   insn (1*2^20 + 20*2^15 + 4*2^12 + 7*2^7 + 0x13),
   shift 7 7 5, regop 23 9 7] ++ copyDigest 23 25 ++
  [addi 25 25 32, shift 20 20 1 true, addi 28 28 (-1), .branch 1 28 0 "open-path",
   .label "open-group", shift 7 20 3, regop 23 22 7, sd 31 23 0,
   addi 24 24 8, addi 27 27 (-1), .branch 1 27 0 "open-position"] ++
  capMarkParents 22 29 ++ capWalk false 22 29 9 0 ++
  [.label "open-done", regop 11 25 15 0 32] ++ halt true

def capCheckCode (depth : Nat) : List Asm :=
  let lower := capLowerHeight depth
  let capLeaves := 2^(capHeight depth)
  [mv 26 11, mv 24 13, mv 8 14, mv 25 15, mv 27 16, regop 22 15 17] ++
  li 6 (32*(lower+1)) ++
  [regop 7 16 6 0 1, .branch 6 17 7 "reject", .branch 0 27 0 "cap-empty"] ++
  li 21 256 ++ li 9 28672 ++ li 18 12288 ++ li 19 capLeaves ++
  [addi 31 0 1, .label "check-position", ld 20 24 0] ++
  copyDigest 25 21 ++ [addi 25 25 32, .jump 1 "leaf"] ++ li 29 lower ++
  [.branch 0 29 0 "check-group", .label "check-path", capAndOne 7 20,
   .branch 0 7 0 "check-left"] ++ copyDigest 21 21 0 32 ++ copyDigest 25 21 ++
  [.jump 0 "check-compress", .label "check-left"] ++ copyDigest 25 21 0 32 ++
  [.label "check-compress"] ++ compressScratch ++
  [addi 25 25 32, shift 20 20 1 true, addi 29 29 (-1), .branch 1 29 0 "check-path",
   .label "check-group", regop 20 20 19, shift 7 20 3, regop 30 9 7,
   shift 7 20 5, regop 23 18 7, ld 6 30 0, .branch 0 6 0 "check-store"] ++
  ((List.range 4).flatMap fun word =>
    [ld 6 21 (8*word), ld 7 23 (8*word), .branch 1 6 7 "reject"]) ++
  [.jump 0 "check-next", .label "check-store"] ++ copyDigest 21 23 ++
  [sd 31 30 0, .label "check-next", addi 24 24 8, addi 27 27 (-1),
   .branch 1 27 0 "check-position"] ++
  capMarkParents 9 19 ++ capWalk true 9 19 18 22 ++
  [.branch 1 25 22 "reject"] ++
  ((List.range 4).flatMap fun word =>
    [ld 6 18 (32+8*word), ld 7 26 (8*word), .branch 1 6 7 "reject"]) ++
  [.jump 0 "accept", .label "cap-empty", .branch 1 17 0 "reject",
   .label "accept"] ++ halt true ++ [.label "reject"] ++ halt false ++ leafSubroutine

/-- Cap images; the complete certificate is assembled separately. -/
def capExperimental (depth : Nat) : Submission :=
  { candidate depth with image := fun program =>
      match program with
      | .commit => (candidate depth).image .commit
      | .opening => ⟨assemble (capOpeningCode depth), []⟩
      | .check => ⟨assemble (capCheckCode depth), []⟩ }
end CommitGolfCandidate
