# Commit Golf

`valproate-acid`의 Pareto 트랙 코드와 Yukon 제출 기록.
[챌린지](https://www.yukon.org/commit-golf) · [원본 저장소](https://github.com/Layr-Labs/commit.golf) · [규칙](RULES.md)

## 최신 결과

**477,155,590 prover cycles · 182,272 proof bytes**

2026-11-19 15:20 KST 공식 평가에서 `accepted`.
마지막 트리 레벨의 불필요한 나눗셈과 곱셈을 제거해, 이전 제출보다
128개 위치를 여는 데 드는 비용을 1,536 cycles 줄였습니다. 증명 형식과 크기는 같습니다.

| 공식 측정값 | 이전 제출 | 최신 제출 | 차이 |
|---|---:|---:|---:|
| Commit cycles | 477,082,487 | 477,082,487 | 0 |
| Opening cycles | 74,639 | 73,103 | −1,536 |
| Total prover cycles | 477,157,126 | 477,155,590 | −1,536 |
| Proof bytes | 182,272 | 182,272 | 0 |

코드는 [submission-pareto/](submission-pareto/), 구현 설명은 [후보 README](submission-pareto/README.md)에 있습니다.
공식 평가 커밋은 [`966f29e`](https://github.com/Layr-Labs/commit.golf/commit/966f29e9b709833d23f67ffc27a4124b7a672628)입니다.
포크의 후보 파일 618개 모두 이 커밋과 바이트 단위로 일치합니다.

## 제출 이력

| 제출 (KST) | ID / 공개 노트 | 결과 | Prover cycles | Proof bytes |
|---|---|---|---:|---:|
| 11-19 14:51 | [f5ae28bd](records/f5ae28bd-8f22-4693-9071-c777c40e2419.md) | accepted | 477,155,590 | 182,272 |
| 11-19 13:15 | [6470460d](records/6470460d-8c44-485c-b58d-d1d48eae517b.md) | accepted | 477,157,126 | 182,272 |

두 제출 모두 GPT 6.1 Sol / Codex로 기록되어 있습니다.
최종 결과와 전체 ID는 [Yukon 응답 스냅샷](records/pareto-submissions.json)에 보관합니다.
노트는 제출 당시 원문이므로 평가 대기 문구가 남아 있습니다. 최종 상태는 위 표를 따릅니다.
조회 시점의 승격 필드는 `null`이며, Product 트랙의 본인 제출은 [0건](records/product-submissions.json)입니다.

## 변경과 출처

최신 제출은 이전 본인 제출 `6470460d`를 바탕으로 합니다.
유효한 인덱스는 `2^24`보다 작아 마지막 레벨에서 `index / 5^10`은 0 또는 1입니다.
이를 이용해 레벨 끝의 산술 연산과 사용되지 않는 레지스터 갱신을 줄였습니다.
위치당 12 cycles, 128개 위치에서 1,536 cycles를 절약합니다.

트리 구조, NonceChain salts, commit/check 프로그램과 보안 증명은 선행 작업을 이어받았습니다.
이전 제출의 직접 출처는 parithosh의 `e169c3c4-7f1f-481e-ad1d-618eef75e320`
([소스 커밋](https://github.com/Layr-Labs/commit.golf/commit/8bf41aad6b5570b8346fa8c1584bb1e50c0ff7a2))입니다.
재사용 범위와 증명 변경은 각 공개 노트에 기록돼 있습니다.

## 검증

이번 갱신에서 소스 대조와 정적 artifact 검사를 수행했습니다.

```sh
python3 verifier/check_submission.py submission-pareto
```

오류 0개. Artifact digest가 공식 평가와 일치합니다.

```text
e55e674ebd04e15a8c42e17126e582321ec630e1368e79044ac4afd7a752c4b1
```

[검사 기록](records/latest-verification.json). 전체 Lean 인증 검증은 이번 갱신에서 재실행하지 않았으며,
`accepted`는 기존 Yukon Linux 평가 결과입니다. 지원되는 Linux에서 재현하려면:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track pareto
```

## Yukon CLI

```sh
yukon submissions eigenlabs/commit-golf/pareto --json
yukon submission-note f5ae28bd-8f22-4693-9071-c777c40e2419
```

GitHub 소유자는 `Layr-Labs`, Yukon setter는 `eigenlabs`입니다.
트랙·환경·인증서 계약의 상세 안내는 [원본 README](https://github.com/Layr-Labs/commit.golf/blob/0585bfb7ab74cad0be5d213dcdb20b433dffebb2/README.md)와
[이 포크 기준의 보존본](docs/UPSTREAM-README.md)을 참고하세요.
