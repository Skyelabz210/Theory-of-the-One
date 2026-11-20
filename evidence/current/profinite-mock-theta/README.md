# Mock theta coefficients, unary shadow, and partition crank execution receipts

The 20 November 2026 audit compiled **367 theorem declarations** with
`leanprover/lean4:v4.27.0-rc1` and its bundled standard library. Of those
declarations, 46 have empty axiom lists. The remaining lists contain only
`propext`, `Classical.choice`, and `Quot.sound`. All ten commands passed
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
| [fifth-one-smoke.log](fifth-one-smoke.log) | 2,135 exact assertions for the five one-subscript fifth-order series |
| [seventh-smoke.log](seventh-smoke.log) | 1,819 exact assertions for the three seventh-order series |
| [third-order-shadow-smoke.log](third-order-shadow-smoke.log) | 9,504 exact assertions for the Laurent normalization of $f$ and the integer coefficients and packets of its unary shadow |
| [quantum-radial-smoke.log](quantum-radial-smoke.log) | 1,579 exact assertions for terminating even-order boundary sums and the order-11 rank/crank specialization |
| [crank-shadow-smoke.log](crank-shadow-smoke.log) | 247 finite partition, character, and signed observation checks |

Four independent finite factor calculations give the integer coefficients of
$f$, $\phi$, $\psi$, and $\chi$ through degree 40. For $\psi$, geometric
coefficients at multiples of $2j-1$ equal one. For $\chi$, the integer oracle
uses $b_0=b_1=1$, $b_{k+2}=b_{k+1}-b_k$ at exponent multiples of $j$.
Each series is checked against its packets, signed-source cylinders, and
finite root evaluations. The log records 6,251 coefficient, packet, and integer-root checks, 408
cylinder checks, and five finite-field root checks per series. Three further
identities contribute 123 degreewise comparisons with Watson in $\mathbb{Z}[q]/(q^{41})$.

The fifth-order suites compare 41 independent integer coefficients per
function. They also exercise packet refinement, signed cylinders, finite
roots, and period admission. The one-subscript suite extends the shifted
identity through degree 41 and independently checks the extra coefficient
of $\phi_1$ at that degree. The two fifth-order suites account for
4,268 assertions.

The seventh-order suite includes 1,206 coefficient and observation checks,
599 initial-summand and cutoff comparisons, and 14 checks of Garvan's
Euler-weighted coefficient relations, for 1,819 assertions.

The four original coefficient suites contribute 32,866 checks. The new
third-order shadow suite compares Laurent coefficients against signed rank
parity through degree 40, checks the signed unary lattice through exponent 625,
and exercises the degree packets modulo 11. Its 9,504 checks bring the complete
total for those five suites to 42,370. The quantum radial suite adds 1,579
assertions on the finite right sides of FOR's formulas. It compares integer
cyclotomic reductions and their finite-field evaluations, including
the order-11 diagonal and off-diagonal rank/crank terms. The six mock theta
and radial suites together contribute 43,949 assertions. In `execution.json`,
`mock_theta_assertions_by_suite` records each suite and
`total_mock_theta_smoke_assertions` records their sum. The original
`mock_theta_smoke_assertions` field counts the third-order suite.

The crank suite checks rank parity through degree 40 and compares all eleven
crank bins against an independent partition count at sizes 6, 17, 28, and 39.
It exercises finite-field characters, signed S6 and S8 readouts, and the
seventh-order size weights. At $N=8$, $t=3$, $z=2$ in $\mathbb F_{23}$, the
$\mathcal F_2$ crank sum is 15 from both the histogram and the S8
transitions. In `execution.json`, `crank_shadow_11_assertions` is 247 and
`total_mock_theta_and_crank_assertions` is 44,196.

Earlier receipts contain 202 declarations and 6,251 mock theta assertions for
$f$ at `853ed93`, then 217 declarations and 12,803 assertions for $f$ and
$\phi$ at `769b724`. The four-function third-order checkpoint reached 247
theorems and 26,779 assertions. [Third-order receipts at `c59b985`](https://github.com/Skyelabz210/Theory-of-the-One/blob/c59b9850f20b9071b7c2ba28b2013cbe55d4d6a4/evidence/current/profinite-mock-theta/execution.json)

The zero-subscript fifth-order checkpoint compiled 267 declarations and
passed 28,912 mock theta assertions. [Receipts at `a028a79`](https://github.com/Skyelabz210/Theory-of-the-One/blob/a028a794b0eccdac35281b09dae825455d0ea73e/evidence/current/profinite-mock-theta/execution.json)

The combined third-order and fifth-order checkpoint compiled 282 declarations
and passed 31,047 mock theta assertions. [Receipts at `63cd3a7`](https://github.com/Skyelabz210/Theory-of-the-One/blob/63cd3a7723ed4a986322b6ad0f83c668dbc4c05b/evidence/current/profinite-mock-theta/execution.json)

The seventh-order checkpoint compiled 299 declarations and passed 32,866 mock theta assertions. [Receipts at `df9dce4`](https://github.com/Skyelabz210/Theory-of-the-One/blob/df9dce4a039ec9d386f72f46925243816025435d/evidence/current/profinite-mock-theta/execution.json)

The crank and shadow-eleven checkpoint compiled 329 declarations and passed
33,113 combined mock theta and crank assertions. [Receipts at `d8d55d9`](https://github.com/Skyelabz210/Theory-of-the-One/blob/d8d55d9aed97ff5c1919d6d5cf3e0f11bc1cac39/evidence/current/profinite-mock-theta/execution.json)

The third-order analytic-shadow coefficient checkpoint compiled 347 declarations
and passed 42,617 combined assertions. [Receipts at `8ffbe91`](https://github.com/Skyelabz210/Theory-of-the-One/blob/8ffbe91a022dd5fba68977d3a788e8f7c3c2f09e/evidence/current/profinite-mock-theta/execution.json)

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
records both groups of five. The [seventh-order review](../../../docs/reviews/2026-11-20-seventh-order-mock-theta.md)
completes the seventeen coefficient constructions. The [crank and shadow review](../../../docs/reviews/2026-11-20-crank-shadow-eleven.md)
covers partition statistics, finite character sums, and the S8 reading hypotheses.
The [analytic review of third-order $f$](../../../docs/reviews/2026-11-20-third-order-analytic-shadow.md)
identifies the complex-analytic operator and the independent numerical
checks. This directory records the standard-library Lean proofs and exact
executions. The [quantum radial review](../../../docs/reviews/2026-11-20-quantum-radial.md)
gives the separate published limit theorem and the numerical checks on four
radial paths. Topological duality and production observation constructors
remain outside these receipts.
