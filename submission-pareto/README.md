# Compact final level of the penta opener

This Pareto candidate builds directly on accepted submission
`6470460d-8c44-485c-b58d-d1d48eae517b`, evaluated commit
`54cd3202df8410cfee713eab785d284d18204b36`. That submission reuses parithosh's
`e169c3c4-7f1f-481e-ad1d-618eef75e320` and its published penta/quad lineage.
The complete commitment and checker images, five-child tree, NonceChain salts,
pinned two-permutation leaves, security construction and proof encoding are inherited.

Every valid index is below `2^24`, hence `index / 5^10 < 2`. At level 10,
the group quotient is zero and the remainder is the incoming node index. The
opener uses `ADDI x25, x6, 0`, loads the fixed group page, adds the trapdoor base,
and dispatches to the existing copy variant. It omits the dead final `x6` update.
Six executed instructions disappear: the two removed arithmetic instructions
cost four cycles each, giving twelve saved cycles per opened position.

The seven unreachable padding words after the exit preserve all five copy-variant
entry addresses. The empty branch and record-loop branch are reencoded for the
shorter main program. The opening image remains 479 words (1,916 bytes).

| Metric | Accepted predecessor | Candidate claim |
|---|---:|---:|
| Commit cycles | 477,082,487 | 477,082,487 |
| Opening cycles, 128 positions | 74,639 | 73,103 |
| Total prover cycles | 477,157,126 | 477,155,590 |
| Opening proof bytes | 182,272 | 182,272 |

`QuadOpeningLevel` derives the final-level range from `div_lt_count`, proves the
shortened head and return path, and retains the level-10 node at the final boundary.
`QuadOpeningLevels` proves `46*count - 6*(count-10)` steps and
`52*count - 12*(count-10)` cycles for up to eleven levels. A complete record takes
511 steps and 571 cycles. Empty openings take 6 cycles; nonempty openings take
`15 + 571 * positions.card`. The certificate targets the exact generated artifact.

The delivered opening bytes passed 117 comparisons against the published accepted
predecessor, including empty, single, maximum, boundary and 128-position inputs.
Every output byte matched, with exactly twelve fewer cycles per position. The
submission-policy check and `lake build CommitGolf CommitGolfTests` passed.
These checks do not establish full certificate acceptance. The local Lean build
and full verifier result are recorded separately in the public submission note;
only a successful verifier run may establish certification.
