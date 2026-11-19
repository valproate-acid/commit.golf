# commit.golf

Design a hiding vector commitment scheme using two independent ideal primitives:

- One **512→256-bit compression function**.
- One **1,600→1,600-bit permutation**, supporting forward and inverse queries.

Both are available together through the fixed `PublicSpec` interface. Solvers can implement
compound functions from these primitives. Every underlying primitive call counts,
including repeated and inverse queries. Submissions cannot declare extra instances,
change widths, or access a built-in variable-input RO or XOF.

## Tracks

- `product`: minimize `(commitCycles + openingCycles) × proofBytes`; edit `submission/`.
- `pareto`: minimize `[commitCycles + openingCycles, proofBytes]` independently; edit `submission-pareto/`.

Both use the same certificate and numeric limits. Use `yukon run --track <track>` or
`python3 scripts/run.py --track <track>` (default: product). `yukon switch <track>`
selects a track without changing Git state.

## Score and certificate

Minimize `(commitCycles + openingCycles) × proofBytes` for one full
commitment and an opening of **128 leaves**. Claims are certified worst-case bounds,
not sample measurements; verification cycles are not scored.

Each submission supplies RISC-V programs for commitment, opening, and checking.
The security-game scheme is derived from those same images. One certificate checks
machine admission, successful honest execution, termination, completeness, query
budgets, proof size, prover cycles, binding, and statistical hiding.

Binding and hiding target 120-bit security, with 2,048-bit logical leaves and 256-bit
commitments. The scheme remains noninteractive. See [RULES.md](../RULES.md) for the
machine interface, cost schedule, and security requirements.

## Submit and validate

**Only the selected track’s submission directory is solver-editable.** All supporting implementation
and proof modules must live inside it. The contract, parameters, oracle definitions,
verifier, build configuration, scripts, and workflows are maintained by the challenge
authors and are not part of a submission.

Use `submission/` (product) or `submission-pareto/` (Pareto) for `Solution.lean`, `claim.json`, `programs.json`, and optional
`CommitGolfCandidate/` modules. The included [salted Merkle submission](../submission/README.md)
provides a complete certificate for the current contract. Run the verifier below to
check the submission against the exact checkout and toolchain being used.
`programs.json` delivers the code bytes and ABI described in the submission README.
The verifier requires a kernel-checked equality between those delivered programs and
the submission named in the certificate, and reports the manifest's SHA-256 digest.
It generates `CommitGolf.Artifact` inside its isolated build project before compiling
the submission. The contract/test build below checks the trusted definitions and
regressions; `scripts/run.py` checks the submitted certificate and artifact equality.
For local development, `python3 scripts/generate_artifact.py` generates the same ignored
module from `submission/programs.json`; use `--refresh` after changing the manifest.
See the [submission README](../submission/README.md#delivered-programs) for the recommended
large-image alias and the limits of equality checking across different representations.

```sh
lake exe cache get
lake build CommitGolf CommitGolfTests
python3 -m unittest discover -s verifier/tests
# Supported Linux host with Landlock and user systemd 257 or newer:
bash scripts/setup.sh
python3 scripts/run.py
```

Keep the checkout and verifier work directory outside `/tmp` and `/var/tmp`:
the sandbox's `PrivateTmp` setting hides those host directories. The verifier
uses a fresh directory under the current directory's `.work/` by default.

Each track’s workflow verifies its own submission directory. There is no oracle
selector: both primitives are available together to every solver.
Reports are `scripts/score.json` (product) and `scripts/pareto/score.json` (Pareto).

The binding game follows the original sampled-function design: sample the two
primitives once, run the adversary, and check both openings against those same
functions. There is no separate finite/infinite binding game or compatibility layer.

## Preserved baseline code

`CommitGolfBaseline/` and `CommitGolfBaseline.lean` preserve the earlier unsalted Merkle
baseline. These historical sources are excluded from the Lake build, verifier inputs,
and permitted submission imports; they target the superseded contract. The current
salted Merkle implementation and its proofs live under `submission/`.

All active oracle definitions are in `CommitGolf/Oracle.lean`. The configurable
family, RO/XOF implementations, lazy-state machinery, and `CommitGolf/Oracle/`
directory have been removed. Oracle regression tests live in `CommitGolfTests.lean`.

## RISC-V execution

`CommitGolf/Riscv.lean` restores the RV64IM interpreter from this repository's
sig.golf-derived history, using the same pinned `riscv-zkvm` dependency. It handles
the fixed compression and forward/inverse permutation syscalls, private randomness,
and halt/failure, recording abstract cycles and public oracle calls separately.
Ordinary instructions cost one cycle; multiplication and division cost four.
Private randomness retains the historical charge of `1 + ceil(bytes / 8)` cycles.
Compression and forward/inverse permutation syscalls each cost eight cycles, with
no additional instruction charge for the syscall. These prices are fixed in Parameters.

`CommitGolf/Programs.lean` defines input loading, output decoding, the executable-derived
scheme and honest machine runs. The certificate and comparator require cycle bounds
for those runs. The interpreter's memory ceiling is 64 GiB; memory is modeled as a
function, not allocated at that size. A full logical vector occupies 4 GiB.
These fixed-parameter bounds measure the specified interpreter's abstract costs;
they do not claim elapsed time on a physical processor.

## Yukon setup

`benchmark.json` defines schema-v2 product and Pareto tracks, sharing setup and verification.
`benchmark.yml` runs product; `benchmark-pareto.yml` runs Pareto. Each uploads its own report.
Yukon must support mixed modes before import. For an existing standalone import, convert it
into the product track first, then import Pareto. Mixed-mode reorgs require `trackScope: "track"`.

`Test PR` compares the PR's exact head and target commits and checks both tracks when required.
Differences outside both submission directories enable the artifact-linkage matrix and maximum-image
admission test. Submission-only PRs on Yukon's same-repository `submissions/*` branches
leave Benchmark execution to Yukon; contract changes on those branches still run the
full checks here. Forks and other branches run Benchmark here.
The final `contract-regressions` check fails if detection or a required Benchmark fails.

Every Benchmark run verifies the full submitted certificate; failed verification produces
no score. Routine dispatches omit the stress tests. Maintainers can explicitly enable
`contract_regressions` for a manual run.

The workflow file alone does not make its final check required. Once a recent eligible
PR run has reported the check, an administrator can activate the additive
[ruleset](../.github/contract-regressions.ruleset.json) before or after the workflow lands.
Landing it on the default branch first avoids blocking PRs that cannot yet report the
gate. Update affected PRs to include the gate and produce fresh `pull_request` checks;
a manual Benchmark dispatch
[does not substitute for that check](https://docs.github.com/en/pull-requests/how-tos/merge-and-close-pull-requests/troubleshooting-required-status-checks#checks-from-some-workflow-jobs-are-not-evaluated).
Then, from this checkout, run:

```sh
gh api --method POST repos/Layr-Labs/commit.golf/rulesets \
  --input .github/contract-regressions.ruleset.json
gh api repos/Layr-Labs/commit.golf/rules/branches/master
```

Confirm that the effective rules include both the existing signed-commit requirement
and `contract-regressions` from GitHub Actions (app 15368). The new rule has no bypass
actors and adds no PR-review or up-to-date-branch requirement. Creating it requires
[repository administration permission](https://docs.github.com/en/rest/repos/rules#create-a-repository-ruleset);
committing this JSON does not activate it.

Before import, install the Yukon GitHub App on the repository and confirm Blacksmith
runner access. The workflow must be available on the default branch for dispatch.
Create the `yukon-unsafe` label for contract changes that invalidate pending scores, then
coordinate the benchmark import with the Yukon team. Repository/app administration and
import are separate from these local files. Yukon owns solver submission PRs and promotion;
do not merge those PRs manually.

Solvers should record reproducible results and provenance in submission notes. Use GitHub
Discussions for partial research when enabled, and remove secrets and private data before
posting either notes or discussions.

## License

See `LICENSE` and `THIRD_PARTY_NOTICES.md`.
