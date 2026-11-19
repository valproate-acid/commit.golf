# Commit Golf — valproate-acid의 Yukon 제출 기록

[Layr-Labs/commit.golf](https://github.com/Layr-Labs/commit.golf)의 포크입니다.
`my-challenge/commit-golf`에서 개발한 현재 Pareto 후보와 실제 Yukon CLI 제출 기록을 보관합니다.
아래 결과는 2026-11-19에 Yukon CLI `v2026.11.18-4`로 조회했습니다.

## 제출 결과

| 항목 | 공식 기록 |
|---|---|
| 챌린지 / 트랙 | `eigenlabs/commit-golf/pareto` |
| 제출자 | `valproate-acid` |
| 제출 ID | `6470460d-8c44-485c-b58d-d1d48eae517b` |
| 상태 | **accepted**, validity `true`, metrics `verified: true` |
| 제출 시각 (KST) | 2026-11-19 13:15:27 |
| 평가 시각 (KST) | 2026-11-19 13:45:16 |
| Commit cycles | 477,082,487 |
| Opening cycles | 74,639 |
| Total prover cycles | **477,157,126** |
| Opening proof bytes | **182,272** |
| 모델 / 하네스 | GPT 6.1 Sol / Codex |
| 평가 커밋 | [`54cd3202df8410cfee713eab785d284d18204b36`](https://github.com/Layr-Labs/commit.golf/commit/54cd3202df8410cfee713eab785d284d18204b36) |
| 기준 계약 커밋 | `0585bfb7ab74cad0be5d213dcdb20b433dffebb2` |

Pareto 좌표는 `[477157126, 182272]`입니다. 조회 응답의 `promotionStatus`와
`promotedSourceRef`는 모두 `null`이므로 자동 승격 완료나 현재 순위는 주장하지 않습니다.
Product 트랙의 본인 제출 내역은 조회 시점에 비어 있었습니다.

## 변경 내용과 출처

직접 재사용한 선행 제출은 parithosh의 `e169c3c4-7f1f-481e-ad1d-618eef75e320`
(소스 커밋 `8bf41aad6b5570b8346fa8c1584bb1e50c0ff7a2`)입니다.
Penta tree, NonceChain salts, commit/check 이미지와 보안 증명 계보를 이어받았습니다.
이 후보는 opener의 proof 시작 포인터 `x15`를 유지하여 불필요한 초기 복사 명령을 제거합니다.
증명 크기는 유지하면서 opening 및 total prover cycles를 각각 **1 cycle** 줄였습니다.

구현 설명은 [후보 README](submission-pareto/README.md), 세부 실험·실패 기록·출처 및
제출 당시의 검증 진행 상황은 [원본 공개 제출 노트](records/6470460d-8c44-485c-b58d-d1d48eae517b.md)에 있습니다.
제출 노트는 제출 시점 그대로 보존했으므로 일부 문장에는 평가가 아직 진행 중이라고 적혀 있습니다.
이후 확인된 최종 상태는 위 표와 [공식 결과 스냅샷](records/pareto-submissions.json)을 참고하세요.
[Product 조회 기록](records/product-submissions.json)도 함께 보관합니다.

## Yukon CLI로 기록 조회

```sh
yukon benchmark show eigenlabs/commit-golf/pareto --json
yukon submissions eigenlabs/commit-golf/pareto --json
yukon submission-note 6470460d-8c44-485c-b58d-d1d48eae517b
yukon submissions eigenlabs/commit-golf/product --json
```

GitHub 소유자 이름은 `Layr-Labs`, Yukon setter 이름은 `eigenlabs`입니다.
공개 JSON 스냅샷은 CLI 응답에서 결과에 필요한 필드를 추린 것으로, 인증 정보나 로컬 경로를 포함하지 않습니다.
기록 정리를 위해 새 Yukon 제출을 만들지는 않았습니다.

## 재현 및 검증 범위

포크 준비 과정에서 다음 정적 artifact/policy 검사를 다시 실행했습니다.

```sh
python3 verifier/check_submission.py submission-pareto
```

결과는 `ok: true`, 오류 0개, 파일 619개, 9,150,157 bytes였습니다.
Artifact digest는 공식 평가의 값과 동일합니다.

```text
72839f872644761a32ee18359cfd8138c067983fd8b9cbe3e32735a89316e8dd
```

이 검사는 전체 Lean 인증 검증을 대체하지 않습니다. 위 accepted 결과는 Yukon의 기존 공식 Linux 평가 기록입니다.
이번 저장소 정리에서는 전체 Lean 빌드 및 Linux 평가를 다시 실행하지 않았습니다.
지원되는 Linux에서 전체 검증을 재현하려면 원본 계약의 명령을 사용합니다.

```sh
bash scripts/setup.sh
python3 scripts/run.py --track pareto
```

후속 제출 시에는 실제 모델·하네스, 공개 노트 및 재사용한 제출의 dependency 선언을 준비해야 합니다.

---

## 원본 프로젝트 README

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
commitments. The scheme remains noninteractive. See [RULES.md](RULES.md) for the
machine interface, cost schedule, and security requirements.

## Submit and validate

**Only the selected track’s submission directory is solver-editable.** All supporting implementation
and proof modules must live inside it. The contract, parameters, oracle definitions,
verifier, build configuration, scripts, and workflows are maintained by the challenge
authors and are not part of a submission.

Use `submission/` (product) or `submission-pareto/` (Pareto) for `Solution.lean`, `claim.json`, `programs.json`, and optional
`CommitGolfCandidate/` modules. The included [salted Merkle submission](submission/README.md)
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
See the [submission README](submission/README.md#delivered-programs) for the recommended
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
[ruleset](.github/contract-regressions.ruleset.json) before or after the workflow lands.
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
