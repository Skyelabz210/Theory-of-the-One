# Evidence status — research draft

## 20 November 2026 — unconditional order-34 to order-10 quantum period

Lean proves the normalized weight-$1/2$ defect at $-1/34$ equals the Eichler period from $-1/24$ to $i\infty$, with multiplier $\sqrt{17/5}$ on the order-10 value. The proof derives the theta transformation on the upper half-plane and proves the two cusp limits from periodic first moments. Every signed source with its primary and same-source mod-17 readings gives the same period after phase normalization of the complete packets. The radial packet convergence theorem uses FOR’s compensated limit for $f+b$ at the positive-angle order-34 root. [Scalar identity](../adapters/MockThetaAnalytic/EichlerBridge.lean) · [Packet identities and radial transfer](../adapters/MockThetaAnalytic/Order34QuantumPackets.lean) · [Current kernel audit](../adapters/MockThetaAnalytic/verification.json)

The 37-module analytic audit checked 343 authored theorems and 828 kernel declarations. Rebuilding the local analytic and imported core modules in a separate checkout produced a byte-identical audit receipt. The standard-library verification also reproduced 44,196 exact mock theta and crank assertions. [Analytic receipt](../adapters/MockThetaAnalytic/verification.json) · [Reproduction commands](../adapters/MockThetaAnalytic/README.md#reproduction)

## 20 November 2026 — source-bound phases, convergence of the period, and mock theta Taylor expansions

Lean proves absolute integrability of the order-34 FKTY period and real analyticity away from $-1/24$. The primary and a same-source mod-17 reading recover both endpoint phases for any signed source. Sources $0$ and $30030$ give equal primary readings and different order-34 phases. For these complete packet arrays, agreement with the integral is equivalent to the single FKTY equation at $-1/34$. [Period](../adapters/MockThetaAnalytic/FKTYPeriodRegularity.lean) · [Signed-source packet theorem](../adapters/MockThetaAnalytic/Order34Source.lean) · [Exact cusp moments](../adapters/MockThetaAnalytic/FKTYCuspMoments.lean)

The integer coefficients of third-order $f$, fifth-order $\chi_0$, and seventh-order $\mathcal F_0$ sum to their defining series on $|q|<1$. FOR’s radial law now suffices for the $f$ packet limit at every primitive even root. [Signed Taylor and radial transfer](../adapters/MockThetaAnalytic/ThirdOrderTaylor.lean) · [Fifth- and seventh-order series](../adapters/MockThetaAnalytic/FifthSeventhHolomorphic.lean)

The 25-module audit covers 243 authored theorems, 150 public and 93 private. Lean checked 589 kernel declarations, including 487 theorem entries with generated helpers. The separate standard-library regression run passed 44,196 exact assertions. [25-module verification](https://github.com/Skyelabz210/Theory-of-the-One/blob/73a0930f49f1ab5ed5278789c824b7143dd9bf8a/adapters/MockThetaAnalytic/verification.json) · [Reproduction commands](../adapters/MockThetaAnalytic/README.md#reproduction)

## 20 November 2026 — the order-34 to order-10 quantum transformation

At $x=-1/34$, the weight-$1/2$ defect for the matrix $\left(\begin{smallmatrix}1&0\\24&1\end{smallmatrix}\right)$ is about $-2.51133957-2.93870810i$. The order-34 endpoint requires quotient resolution divisible by 17. The order-10 endpoint uses the primary alone. Independent finite sums and numerical quadrature of the FKTY theta period agree within $1.07\times10^{-46}$.
Lean proves the finite endpoint formulas and identifies the period integrand with half the differential shadow. The transport theorem takes FKTY’s analytic law as a hypothesis. The 16-module audit covers 149 authored theorems, including 66 in the four new modules, and 360 kernel declarations.
[Specialization and observation formulas](../docs/reviews/2026-11-20-order-34-to-10.md)
· [Checkpoint kernel audit](https://github.com/Skyelabz210/Theory-of-the-One/blob/1915b7908bbc737c76d6435668319cbc30134d65/adapters/MockThetaAnalytic/verification.json)
· [Numerical receipt](current/quantum-radial/transport34.json)

## 20 November 2026 — infinite differentiation of the third-order completion

Lean proves $\xi_{1/2}M_f=4\Theta$ on the upper half-plane directly from the
named hypergeometric $f$ and its infinite Fourier correction. It proves the
termwise real derivative and classifies the five identically vanishing
projected shadows modulo 11. The expanded analytic package contains 83
explicitly declared theorems across 12 modules, 58 public and 25 private.
The kernel audited 195 constants, including 164 theorem entries when generated
helpers are counted.
[Infinite completion and source map](https://github.com/Skyelabz210/Theory-of-the-One/blob/39d990a079c80407b377a574c78b96f72c842408/docs/reviews/2026-11-20-third-order-analytic-shadow.md#differentiating-the-completed-function)
· [Analytic kernel audit](https://github.com/Skyelabz210/Theory-of-the-One/blob/39d990a079c80407b377a574c78b96f72c842408/adapters/MockThetaAnalytic/verification.json)

## 20 November 2026 — complex-analytic shadow and radial operators in Lean

The separate Mathlib adapter compiled 45 explicitly declared theorems across
six modules, 36 public and nine private. The kernel audit covered 124 constants,
including 103 theorem entries when compiler-generated helpers are counted.
An independent checkout rebuilt the core and all six analytic modules and
produced a byte-identical receipt. The proofs establish absolute convergence of the signed unary series, its degree
projections, and sign reversal under the conjugate differential operator.
For every finite completion the derivative gives the corresponding unary
sum. These derivatives converge to the analytic shadow for every point in
the upper half-plane. The radial transfer theorem takes the interior Taylor
identity and FOR limit as hypotheses and gives cutoffs for finite packet
evaluations. For the BOPR specialization at $w=1$, the adapter proves the
terminating cusp values, normalized translation law, and exact prime-11
polynomial. BOPR supplies the inversion law, independently tested against
the eta period at three cusps.
[Result and exact hypotheses](https://github.com/Skyelabz210/Theory-of-the-One/blob/4b90453cb7fe510f9afb790a2d57ca2b8b52e6e2/docs/reviews/2026-11-20-third-order-analytic-shadow.md#complex-analysis-in-lean)
· [Analytic kernel audit](https://github.com/Skyelabz210/Theory-of-the-One/blob/4b90453cb7fe510f9afb790a2d57ca2b8b52e6e2/adapters/MockThetaAnalytic/verification.json)

## 20 November 2026 — rank/crank quantum radial values

FOR's radial theorem identifies the compensated limit of the third-order
$f$ at primitive even roots and, in a separate specialization, the rank/crank
limit at the eleventh root. The Lean package proves termination and packet
evaluation of the finite boundary polynomial and the diagonal rank/crank
formula. The audit compiled 367 declarations, including 20 in `QuantumRadial`.
The combined exact suites passed 44,196 assertions, including 1,579 for the
radial formulas. The numerical study compares four radial approaches with
the source predictions.
[Proof, literature, and domain map](https://github.com/Skyelabz210/Theory-of-the-One/blob/6e6666c3a56247c2907c714b78b0aac11f59220a/docs/reviews/2026-11-20-quantum-radial.md)
· [Exact execution](https://github.com/Skyelabz210/Theory-of-the-One/blob/6e6666c3a56247c2907c714b78b0aac11f59220a/evidence/current/profinite-mock-theta/quantum-radial-smoke.log)
· [Numerical evidence](https://github.com/Skyelabz210/Theory-of-the-One/blob/6e6666c3a56247c2907c714b78b0aac11f59220a/evidence/current/quantum-radial/README.md)

## 20 November 2026 — analytic shadow of the third-order f

For the normalized completion with holomorphic part $q^{-1}f(q^{24})$, the
review derives the weight-$3/2$ unary shadow and its eleven Fourier-degree
projections from Zwegers' real-analytic modular form. The standard-library
audit compiled 347 declarations, including 18 for the signed square coefficients and Laurent normalization. The new executable
suite passed 9,504 exact checks, bringing the combined mock theta and crank
total to 42,617. Numerical differentiation tests
the completed function at three points and every projection at one point.
[Normalization, derivation, and proof map](https://github.com/Skyelabz210/Theory-of-the-One/blob/8ffbe91a022dd5fba68977d3a788e8f7c3c2f09e/docs/reviews/2026-11-20-third-order-analytic-shadow.md)
· [Proof audit](https://github.com/Skyelabz210/Theory-of-the-One/blob/8ffbe91a022dd5fba68977d3a788e8f7c3c2f09e/evidence/current/profinite-mock-theta/verification.json)
· [Exact execution](https://github.com/Skyelabz210/Theory-of-the-One/blob/8ffbe91a022dd5fba68977d3a788e8f7c3c2f09e/evidence/current/profinite-mock-theta/third-order-shadow-smoke.log)
· [Numerical execution](https://github.com/Skyelabz210/Theory-of-the-One/blob/8ffbe91a022dd5fba68977d3a788e8f7c3c2f09e/evidence/current/analytic-shadow/numerical.json)

## 20 November 2026 — partition crank and shadow prime 11

Lean proves the size-six rank and crank histograms, an integer criterion for
uniformity modulo 11, and evaluation of all three finite seventh-order
weighted crank sums from authentic per-partition S8 transitions. The independent
crank check counts each residue class at sizes 6, 17, 28, and 39.
[Definitions, proofs, and finite examples](https://github.com/Skyelabz210/Theory-of-the-One/blob/d8d55d9aed97ff5c1919d6d5cf3e0f11bc1cac39/docs/reviews/2026-11-20-crank-shadow-eleven.md)

The audit compiled 329 declarations, including 169 in the profinite and mock
theta modules and 30 in the crank and shadow modules. All eight commands
passed. The four mock theta suites passed 32,866 assertions and the crank suite
passed 247, for 33,113 combined. The closure smoke separately passed 1,809
comparison/divmod/GCD pairs and four controls.
[Execution](https://github.com/Skyelabz210/Theory-of-the-One/blob/d8d55d9aed97ff5c1919d6d5cf3e0f11bc1cac39/evidence/current/profinite-mock-theta/execution.json) · [Proof audit](https://github.com/Skyelabz210/Theory-of-the-One/blob/d8d55d9aed97ff5c1919d6d5cf3e0f11bc1cac39/evidence/current/profinite-mock-theta/verification.json)
· [Crank checks](https://github.com/Skyelabz210/Theory-of-the-One/blob/d8d55d9aed97ff5c1919d6d5cf3e0f11bc1cac39/evidence/current/profinite-mock-theta/crank-shadow-smoke.log)

## 20 November 2026 — the three seventh-order functions

The three seventh-order coefficient families complete the 17 original functions.
Their formal definitions prove the denominator reciprocal and the exact
leading coefficient of each summand. Each family specializes the packet,
cylinder, and coupled-anchor evaluation theorems.
[Proof and source map](https://github.com/Skyelabz210/Theory-of-the-One/blob/df9dce4a039ec9d386f72f46925243816025435d/docs/reviews/2026-11-20-seventh-order-mock-theta.md)

The audit passed 299 theorem declarations (169 in the profinite and mock
theta modules). The four mock theta suites passed 32,866 exact assertions,
including 1,819 in the seventh-order suite. The separate closure smoke passed
1,809 comparison/divmod/GCD pairs and four controls.
[Execution](https://github.com/Skyelabz210/Theory-of-the-One/blob/df9dce4a039ec9d386f72f46925243816025435d/evidence/current/profinite-mock-theta/execution.json) · [Proof audit](https://github.com/Skyelabz210/Theory-of-the-One/blob/df9dce4a039ec9d386f72f46925243816025435d/evidence/current/profinite-mock-theta/verification.json)
· [Seventh-order checks](https://github.com/Skyelabz210/Theory-of-the-One/blob/df9dce4a039ec9d386f72f46925243816025435d/evidence/current/profinite-mock-theta/seventh-smoke.log)

## 20 November 2026 — both original fifth-order groups

All ten fifth-order functions have formal coefficients, residue packets,
cylinders, and a finite evaluation theorem at the coupled-anchor period.
With the original four third-order functions, coverage is 14 of 17.
[Fifth-order proof and source map](https://github.com/Skyelabz210/Theory-of-the-One/blob/63cd3a7723ed4a986322b6ad0f83c668dbc4c05b/docs/reviews/2026-11-20-fifth-order-mock-theta.md)

The fresh Lean build and audit passed 282 theorem declarations, 152 in the
profinite and mock theta modules. The three mock theta suites passed 31,047
exact assertions (26,779 third-order, 2,133 fifth-order zero, 2,135
fifth-order one). The separate closure smoke passed 1,809 comparison/divmod/GCD
pairs and four controls.
[Proof audit](https://github.com/Skyelabz210/Theory-of-the-One/blob/63cd3a7723ed4a986322b6ad0f83c668dbc4c05b/evidence/current/profinite-mock-theta/verification.json) · [Execution](https://github.com/Skyelabz210/Theory-of-the-One/blob/63cd3a7723ed4a986322b6ad0f83c668dbc4c05b/evidence/current/profinite-mock-theta/execution.json)
· [One-subscript smoke](https://github.com/Skyelabz210/Theory-of-the-One/blob/63cd3a7723ed4a986322b6ad0f83c668dbc4c05b/evidence/current/profinite-mock-theta/fifth-one-smoke.log)

## 20 November 2026 — fifth-order series, subscript zero

The five named series $f_0,\phi_0,\psi_0,\chi_0,F_0$ join the four original
third-order functions. Each has a coefficient formula, support bound, packet
and cylinder construction, and finite root evaluation under the coupled-anchor
period contract. [Fifth-order formalization](https://github.com/Skyelabz210/Theory-of-the-One/blob/a028a794b0eccdac35281b09dae825455d0ea73e/docs/reviews/2026-11-20-fifth-order-mock-theta.md)

The fresh audit passed 267 theorem declarations. The fifth-order zero-subscript
suite passed 2,133 exact assertions and the third-order suite passed 26,779,
for 28,912 mock theta assertions in total. The existing closure smoke passed
1,809 comparison/divmod/GCD pairs and four controls.
[Audit](https://github.com/Skyelabz210/Theory-of-the-One/blob/a028a794b0eccdac35281b09dae825455d0ea73e/evidence/current/profinite-mock-theta/verification.json) · [Execution](https://github.com/Skyelabz210/Theory-of-the-One/blob/a028a794b0eccdac35281b09dae825455d0ea73e/evidence/current/profinite-mock-theta/execution.json)
· [Zero-subscript smoke](https://github.com/Skyelabz210/Theory-of-the-One/blob/a028a794b0eccdac35281b09dae825455d0ea73e/evidence/current/profinite-mock-theta/fifth-zero-smoke.log)

## 20 November 2026 — original third-order group

All four named coefficient constructions reach the finite transform through the same
coupled-anchor criterion. The implementation, mathematical sources, and bounds
of each proof are recorded in the [formalization review](../docs/reviews/2026-11-20-profinite-mock-theta-formalization.md).

| Executed check | Result | Receipt |
|---|---|---|
| Fresh temporary proof build and transitive axiom audit | 247 declarations passed, including 14 each in `MockThetaPsi` and `MockThetaChi` | [Proof receipt](https://github.com/Skyelabz210/Theory-of-the-One/blob/c59b9850f20b9071b7c2ba28b2013cbe55d4d6a4/evidence/current/profinite-mock-theta/verification.json) |
| Pinned Lake package build | Passed | [Build log](https://github.com/Skyelabz210/Theory-of-the-One/blob/c59b9850f20b9071b7c2ba28b2013cbe55d4d6a4/evidence/current/profinite-mock-theta/lake-build.log) |
| Concrete comparison/divmod/GCD execution | 1,809 pairs and four controls | [Closure smoke](https://github.com/Skyelabz210/Theory-of-the-One/blob/c59b9850f20b9071b7c2ba28b2013cbe55d4d6a4/evidence/current/profinite-mock-theta/closure-smoke.log) |
| Mock theta execution | 26,779 exact assertions passed, including 41 independent coefficients per series and 123 comparisons with Watson's relations | [Smoke log](https://github.com/Skyelabz210/Theory-of-the-One/blob/c59b9850f20b9071b7c2ba28b2013cbe55d4d6a4/evidence/current/profinite-mock-theta/mock-theta-smoke.log) |

The earlier $f$ implementation at `853ed93` passed 202 theorem declarations and
6,251 mock theta assertions. The $f$, $\phi$ implementation at `769b724` passed 217
declarations and 12,803 assertions. Each revision records its source hashes
and logs. [$f$ receipts](https://github.com/Skyelabz210/Theory-of-the-One/tree/853ed937d0fa3545683d668e72f6439b599529b5/evidence/current/profinite-mock-theta) · [$f$, $\phi$ receipts](https://github.com/Skyelabz210/Theory-of-the-One/tree/769b724802ba1fd2e042718ac2dbc95b79d6fed1/evidence/current/profinite-mock-theta)

## 20 November 2026 — research archive

The [arbitrary-moduli and profinite-bridge package](../foundations/profinite_bridge/2026-11-20/README.md) preserves both completed papers, their editable sources, reproducible checks, and source-pinned receipts. Its manifest and evidence READMEs distinguish fresh finite execution from historical Lean receipts and from the analytic research program. This archive commit adds no new Lean declarations. The subsequent formalization must carry its own compiler and axiom-audit receipt.

The repository is currently public. The visibility description in the following historical review records the state observed on its date.

## 16 November 2026 — foundation review

Reviewed on 16 November 2026 for the then-private repository `Skyelabz210/Theory-of-the-One`. Reviewed source: `f66b9a74eecf76ce5b4ecc978879b60d17f71df7`, all 61 tracked files. Draft marker: `ceb9e0a93a67894d737148cecc04fcc382bfc8df`. The delivered edits and evidence follow that source review.

| Executed check | Result | Receipt |
|---|---|---|
| Official pinned Lean archive digest | Matched published SHA256 | [Compiler and execution](current/lean/execution.json) |
| Fresh temporary proof build and transitive axiom audit | 130 declarations passed; no compiler warnings; no reused project oleans | [Verification](current/lean/verification.json), [log](current/lean/verification.log) |
| Standard Lake package build | Passed, 13 jobs | [Build log](current/lean/lake-build.log) |
| Concrete Lean comparison/divmod/GCD execution | 1,809 pairs plus four boundary/refusal controls passed | [Smoke log](current/lean/closure-smoke.log) |
| Supplied Python mathematical checker | 821,881 assertions passed, zero failures | [Result](current/residue_core_verification.json), [execution](current/execution.json) |
| Independent finite observation-partition checks | 341,562 checks passed | [Result](current/audit/independent_partition_checks.json) |
| Reference-runner failure control after repair | Nonzero exit recorded; old PASS report absent | [Failure control](current/reference-failure-control.json) |
| Proof-runner failure control after repair | Compilation failure; old PASS receipt absent | [Both reproducible failure controls](current/audit/failure_controls.json) |

Lean pin: `leanprover/lean4:v4.27.0-rc1`, bundled standard library, no Mathlib dependency. Thirty declarations have no axiom dependencies. The remaining declarations use only `propext`, `Classical.choice` and `Quot.sound`; the package is not wholly axiom-free. The current Lean source hashes match the supplied historical receipt. No Lean theorem was weakened or changed during this review.

The reference checker's syntax audit found zero floating-point literals and zero true-division AST nodes. These syntax counts supplement inspection; they are not a whole-runtime dataflow proof. All eight supplied PNG figures regenerated byte-identically in the audit environment. SVG metadata is not byte-stable. Manual visual-review metadata belongs to the reviewed images and must be renewed after changing figures.

The [deep analysis](../docs/reviews/2026-11-16-deep-analysis.md) and [formal coverage map](../docs/reviews/2026-11-16-formal-coverage.md) separate written theorem sections, compiled declarations, concrete executable semantics, and machine integration obligations. The tests do not extend bounded natural-number divmod to signed or unbounded inputs. The architecture's source/frame/epoch admission must still be enforced by an integration layer.

Historical source inspections of other repositories remain dated evidence. This review did not execute NINE65 or certify production integration, performance, cryptographic security, physical models or continuum claims. Original archives and private Drive links remain excluded.

Historical formal receipts are unchanged in `historical/formal/`. Original packet hashes, the earlier publication manifest and editorial record remain historical artifacts. Current packet and repository manifests describe this delivered tree; see [audit changes](current/audit_changes.json).
