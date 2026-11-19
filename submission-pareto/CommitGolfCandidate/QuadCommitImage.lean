import CommitGolf.Programs

/-! Penta commit machine image, independent of the opening and checker images.
Setup and the NonceChain generator (entered from word 17, after the root) as before; the pinned
two-permutation leaf body (8d2a211) unrolled 4096 times writes leaf `i`'s second reply into slot
`i % 5` of level-0 group `i / 5`. The first pass runs leaves 0 .. 4095, then the loop re-enters at
leaf 1 for 4096 passes of 4095 leaves (2^24 leaves in all). Then the ragged slots of the last
level-0 group are cleared, and levels 1 .. 10 run node passes (an unrolled loop body plus an
unrolled tail, then clearing the ragged slots of the level's last group). The root node is written
to trapdoor offset 32 and copied to the commitment by the unchanged root code.
Salt loads use centered 256-leaf windows (signed immediates `16*(u%256)` around x22, x7 = 4096,
rebase at `u%256 = 127`); the generator body is unrolled 288 times. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

/-- Offset encoded in the signed 12-bit destination immediate (45-leaf centered window). -/
def slotImmediate (u : Nat) : BitVec 12 :=
  BitVec.ofInt 12 (-1536 + 368 * Int.ofNat ((u % 45) / 5) + 32 * Int.ofNat (u % 5))

def leafWords (u : Nat) : List (BitVec 32) :=
  [0xfe050613, 0x00000073, 0x03850513, 0x00a53023,
   BitVec.ofNat 32 (0x000b3f83 + 1048576 * (16 * (u % 256))), 0x01f53423,
   BitVec.ofNat 32 (0x008b3f83 + 1048576 * (16 * (u % 256))), 0x01f53823,
   BitVec.ofNat 32 (0x000a0613 + 1048576 * (slotImmediate u).toNat),
   0x00000073, 0x0c850513] ++
  (if u % 45 = 44 then [0x6f060a13] else []) ++
  (if u % 256 = 127 then [0x007b0b33] else []) ++
  (if u = 4095 then [0xff0b0b13] else [])

def setupWords : List (BitVec 32) :=
  [0x00058413, 0x00060493, 0x00050913, 0x00001a37, 0x600a0a13, 0x01448a33, 0x6c001b37, 0x000b0b13,
   0x01648b33, 0x00200293, 0xf50b0513, 0x01800593, 0x00058593, 0x00000073, 0x00000293, 0x0c800593,
   0x00100693, 0x7d1e606f, 0x00c69393]

/-- `beq x10, x8` leaves the loop (over 16 never-executed padding words); otherwise jump back to leaf 1. -/
def leafLatchWords : List (BitVec 32) :=
  [0x04850463, 0xe79d306f,
   0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013]

/-- Clear slots 1 .. 4 of the last level-0 group (relative to the last leaf's slot in x12). -/
def leafZeroWords : List (BitVec 32) :=
  [0x02063023, 0x02063423, 0x02063823, 0x02063c23, 0x04063023, 0x04063423, 0x04063823, 0x04063c23,
   0x06063023, 0x06063423, 0x06063823, 0x06063c23, 0x08063023, 0x08063423, 0x08063823, 0x08063c23]

/-- One node: permutation call, next input group, next output slot (+240 after slot 4). -/
def nodeWords (t : Nat) : List (BitVec 32) :=
  [0x00000073, 0x17050513, if t = 4 then 0x0f060613 else 0x02060613]

def nodeCode (n : Nat) : List (BitVec 32) := (List.range n).flatMap (fun p => nodeWords (p % 5))

/-- Loop body nodes, loop iterations, tail nodes and cleared words of level `m`. -/
def levelS : Nat → Nat
  | 1 => 29430
  | 2 => 14585
  | 3 => 7895
  | 4 => 4470
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | _ => 0

def levelQ : Nat → Nat
  | 1 => 114
  | 2 => 46
  | 3 => 17
  | 4 => 6
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | _ => 0

def levelR : Nat → Nat
  | 1 => 424
  | 2 => 179
  | 3 => 3
  | 4 => 24
  | 5 => 5369
  | 6 => 1074
  | 7 => 215
  | 8 => 43
  | 9 => 9
  | 10 => 2
  | _ => 0

def levelZ : Nat → Nat
  | 1 => 4
  | 2 => 4
  | 3 => 8
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | 7 => 0
  | 8 => 8
  | 9 => 4
  | 10 => 12
  | _ => 0

/-- x10 := level m-1 group 0, x12 := level m slot 0, x21 := slot after the loop part. -/
def levelSetupWords : Nat → List (BitVec 32)
  | 1 => [0x00001537, 0xfd850513, 0x00a48533, 0x4999c637, 0x00060613, 0x00c48633, 0x5851aab7, 0x840a8a93,
   0x01548ab3]
  | 2 => [0x4999c537, 0xfd850513, 0x00a48533, 0x58523637, 0x00060613, 0x00c48633, 0x5b43aab7, 0x6a0a8a93,
   0x01548ab3]
  | 3 => [0x58523537, 0xfd850513, 0x00a48533, 0x5b43f637, 0x00060613, 0x00c48633, 0x5bdabab7, 0xad0a8a93,
   0x01548ab3]
  | 4 => [0x5b43f537, 0xfd850513, 0x00a48533, 0x5bdac637, 0x00060613, 0x00c48633, 0x5bf8eab7, 0xec0a8a93,
   0x01548ab3]
  | 5 => [0x5bdac537, 0xfd850513, 0x00a48533, 0x5bf90637, 0x00060613, 0x00c48633, 0x5bf90ab7, 0x000a8a93,
   0x01548ab3]
  | 6 => [0x5bf90537, 0xfd850513, 0x00a48533, 0x5bff2637, 0x00060613, 0x00c48633, 0x5bff2ab7, 0x000a8a93,
   0x01548ab3]
  | 7 => [0x5bff2537, 0xfd850513, 0x00a48533, 0x5c007637, 0x00060613, 0x00c48633, 0x5c007ab7, 0x000a8a93,
   0x01548ab3]
  | 8 => [0x5c007537, 0xfd850513, 0x00a48533, 0x5c00c637, 0x00060613, 0x00c48633, 0x5c00cab7, 0x000a8a93,
   0x01548ab3]
  | 9 => [0x5c00c537, 0xfd850513, 0x00a48533, 0x5c00e637, 0x00060613, 0x00c48633, 0x5c00eab7, 0x000a8a93,
   0x01548ab3]
  | 10 => [0x5c00e537, 0xfd850513, 0x00a48533, 0x5c010637, 0x00060613, 0x00c48633, 0x5c010ab7, 0x000a8a93,
   0x01548ab3]
  | _ => []

def levelLatchWords : Nat → List (BitVec 32)
  | 1 => [0x01560463, 0xc75a906f]
  | 2 => [0x01560463, 0xc50d506f]
  | 3 => [0x01560463, 0xde9e806f]
  | 4 => [0x01560463, 0xe75f206f]
  | _ => []

/-- `sd x0, 8t(x12)`: clear the ragged slots after the last node. -/
def levelZeroWords : Nat → List (BitVec 32)
  | 1 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 2 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 3 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23, 0x02063023, 0x02063423, 0x02063823, 0x02063c23]
  | 4 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 5 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 6 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 7 => []
  | 8 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23, 0x02063023, 0x02063423, 0x02063823, 0x02063c23]
  | 9 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23]
  | 10 => [0x00063023, 0x00063423, 0x00063823, 0x00063c23, 0x02063023, 0x02063423, 0x02063823, 0x02063c23,
   0x04063023, 0x04063423, 0x04063823, 0x04063c23]
  | _ => []

def levelCode (m : Nat) : List (BitVec 32) :=
  levelSetupWords m ++ (if levelQ m = 0 then [] else nodeCode (levelS m) ++ levelLatchWords m) ++
    nodeCode (levelR m) ++ levelZeroWords m

def levelsCode : List (BitVec 32) :=
  levelCode 1 ++ levelCode 2 ++ levelCode 3 ++ levelCode 4 ++ levelCode 5 ++
  levelCode 6 ++ levelCode 7 ++ levelCode 8 ++ levelCode 9 ++ levelCode 10

/-- x10 := level-10 group 0, x12 := trapdoor + 32 (old heap node 1), one node. -/
def rootSetupWords : List (BitVec 32) :=
  [0x5c010537, 0xfd850513, 0x00a48533, 0x02048613, 0x00000073]

def genWords : List (BitVec 32) :=
  [0x000b0613, 0x100023b7, 0x00038393, 0x016383b3] ++
  (List.replicate 288 [0x00000073, 0x0b050513, 0x0b060613]).flatten ++
  [0xa8766063, 0x00090513, 0x00048613, 0xa981806f]

def rootWords : List (BitVec 32) :=
  [0x0204bf83, 0x01f43023, 0x0284bf83, 0x01f43423, 0x0304bf83, 0x01f43823, 0x0384bf83, 0x01f43c23, 0x00100293, 0x00000513, 0x00000073] ++ genWords

def leafCode : List (BitVec 32) := (List.range 4096).flatMap leafWords

def image : Image := ⟨setupWords ++ leafCode ++ leafLatchWords ++ leafZeroWords ++ levelsCode ++
  rootSetupWords ++ rootWords, []⟩

/-- Only the commit image and the common layout are fixed here. -/
def submission (opening checker : Image) : Submission where
  sizes := ⟨2080378880, 23890755584⟩
  layout := ⟨4096,4294971392,4294971424,6375350304,6509568096,10804535392⟩
  image := fun | .commit => image | .opening => opening | .check => checker
  steps := fun | .commit => 1073807360 | .opening => 17179934720 | .check => 34359803904

/-- Number of ordinary machine steps of the intended successful trace (seed draw, generator, tree). -/
def executionSteps : Nat := 202164568
/-- Sum of the phase ledger; reachability is proved in `QuadNonceCommitTranscript`. -/
def executionCycles : Nat := 477082487
def executionCalls : Nat := 39273988

theorem submission_commit_image (opening checker : Image) :
    (submission opening checker).image .commit = image := rfl

theorem enough_commit_fuel (opening checker : Image) :
    executionSteps ≤ (submission opening checker).steps .commit := by
  change executionSteps ≤ 1073807360
  decide

end TwoPermutationPrototype.Quad.Commit
