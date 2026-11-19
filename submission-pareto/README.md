# Penta opener with a preserved ABI proof pointer

This Pareto candidate directly reuses parithosh's published submission
`e169c3c4-7f1f-481e-ad1d-618eef75e320`, source commit
`8bf41aad6b5570b8346fa8c1584bb1e50c0ff7a2`.
Its complete commit/check images, five-child tree, NonceChain salts, binding and
hiding proofs are retained. The predecessor credits its earlier penta/quad
lineage, pinned two-permutation leaves, C2 salt windows and C3 generator unrolling;
those inherited contributions are not new work here.

The opener retains the ABI proof start in `x15` throughout every record and uses
it directly when computing the returned length. Removing the initial
`ADDI x20, x15, 0` saves one executed instruction and one abstract cycle for every
opening, including an empty opening. Main-program word indices move down by one;
an unreachable padding word after the exit keeps the five copy-variant entry
addresses unchanged. The delivered bytes and the Lean decode/execution proofs
change together. The proof bytes and cryptographic construction remain the same.

| Metric | Predecessor | This candidate |
|---|---:|---:|
| Commit cycles | 477,082,487 | 477,082,487 |
| Opening cycles, 128 positions | 74,640 | 74,639 |
| Total prover cycles | 477,157,127 | 477,157,126 |
| Opening proof bytes | 182,272 | 182,272 |

`QuadOpeningRecord.RecordAt.begin` proves that `x15` survives all record runs.
`QuadOpeningABI` proves exact costs of 6 cycles for empty openings and
`15 + 583 * positions.card` for nonempty openings. The final certificate is about
the exact `programs.json` artifact, not an independent abstract scheme.

Local verification evidence and the authoritative Linux evaluation are recorded
in the public Yukon submission note. Development uses macOS; its local comparator
mode is unsandboxed and must not be confused with the official Linux runner.
