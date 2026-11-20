# Exact mock theta coefficient bridge: execution receipts

The 20 November 2026 audit compiled **267 theorem declarations** with
`leanprover/lean4:v4.27.0-rc1` and its bundled standard library. Of those
declarations, 41 have empty axiom lists. The remaining lists contain only
`propext`, `Classical.choice`, and `Quot.sound`. All 5 commands passed
without compiler warnings.

| File | Meaning |
|---|---|
| [execution.json](execution.json) | Commands, compiler binary hashes, source hashes, base revision, exit status, and executed smoke assertion count |
| [verification.json](verification.json) | Every compiled proof source, theorem, and transitive axiom dependency |
| [verification.log](verification.log) | Fresh temporary compilation and axiom-query output; no project oleans reused |
| [proof-audit.log](proof-audit.log) | Summary output from the proof checker |
| [lake-build.log](lake-build.log) | Package build using the registered module graph |
| [closure-smoke.log](closure-smoke.log) | Existing 1,809 concrete comparison/divmod/GCD pairs and four controls |
| [mock-theta-smoke.log](mock-theta-smoke.log) | 26,779 exact assertions for the four third-order series and three Watson relations |
| [fifth-zero-smoke.log](fifth-zero-smoke.log) | 2,133 exact assertions for the five zero-subscript fifth-order series |

Four independent finite factor calculations give the integer coefficients of
$f$, $\phi$, $\psi$, and $\chi$ through degree 40. For $\psi$, geometric
coefficients at multiples of $2j-1$ equal one. For $\chi$, the integer oracle
uses $b_0=b_1=1$, $b_{k+2}=b_{k+1}-b_k$ at exponent multiples of $j$.
Each series is checked against its packets, signed-source cylinders, and
finite root evaluations. The log records 6,251 coefficient, packet, and integer-root checks, 408
cylinder checks, and five finite-field root checks per series. Three further
identities contribute 123 degreewise comparisons with Watson in $\mathbb{Z}[q]/(q^{41})$.

The complete mock theta total is 28,912. In `execution.json`,
`mock_theta_assertions_by_suite` records each suite and
`total_mock_theta_smoke_assertions` records their sum. The original
`mock_theta_smoke_assertions` field counts the third-order suite.

Earlier receipts contain 202 declarations and 6,251 mock theta assertions for
$f$ at `853ed93`, then 217 declarations and 12,803 assertions for $f$ and
$\phi$ at `769b724`. The four-function third-order checkpoint reached 247
theorems and 26,779 assertions. [Third-order receipts at `c59b985`](https://github.com/Skyelabz210/Theory-of-the-One/blob/c59b9850f20b9071b7c2ba28b2013cbe55d4d6a4/evidence/current/profinite-mock-theta/execution.json)

The current receipt records the base commit and hashes of
the files used in this run.
[$f$ receipts](https://github.com/Skyelabz210/Theory-of-the-One/tree/853ed937d0fa3545683d668e72f6439b599529b5/evidence/current/profinite-mock-theta) · [$f$, $\phi$ receipts](https://github.com/Skyelabz210/Theory-of-the-One/tree/769b724802ba1fd2e042718ac2dbc95b79d6fed1/evidence/current/profinite-mock-theta) · [Current execution](execution.json)

From the repository root, with the pinned Lean/Lake installation available:

```sh
python3 tools/verify_profinite_mock_theta.py --lean lean
```

Supply `--lean /path/to/the/pinned/bin/lean` when it is not on PATH. Lake must be
in the same installation. The runner first audits a fresh temporary proof build,
then builds the Lake package and executes the registered smoke modules. It invalidates
its previous receipt before a run and writes a failed execution receipt if a
check fails. Python 3.11 or newer suffices; no external Python dependencies or
Mathlib download are needed.

The [formalization review](../../../docs/reviews/2026-11-20-profinite-mock-theta-formalization.md)
covers the third-order group. The [fifth-order review](../../../docs/reviews/2026-11-20-fifth-order-mock-theta.md)
records the newer formulas and execution scope. Topological duality, infinite analytic
evaluation, radial asymptotics, analytic shadows, and production observation
constructors are outside these receipts.
