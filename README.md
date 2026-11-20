# Theory of the One — Draft

> **Research draft.** Active coherence review and formal verification. See [evidence status](evidence/STATUS.md) for the scope of checked results.

**Configurable Residue Arithmetic Machines**  
Anthony Diaz (Acid) · Research repository

**Theory of the One develops the consequences of Euclid's account of unity, number, and measurement for exact computation.** It begins with the definitions as written, identifies their edition, and makes the mathematical derivations explicit.

**CRAM is the configurable machine architecture developed from that foundation.** It uses coordinated residue observations as operative state. Its contracts specify what those observations determine and how operators preserve their meaning across applications.

Read [the foundational chain](docs/EUCLID_TO_CRAM.md): **Euclid's text → proved consequences → CRAM machine architecture → applications**. Modern notation expresses the derivations; the quoted source text retains its wording. Each result states its definitions and hypotheses, and each machine design identifies its implementation choices.

The name follows the author's current expansion: **Configurable Residue Arithmetic Machines**. Earlier sources using “Chimera” are retained as historical terminology.

## The organizing idea

A computation need not carry a reconstructed integer or a stored scalar winding to answer an exact arithmetic question. It can preserve authentic residue and anchor evidence and derive the required observable when needed.

For adjacent moduli, with `M > 0`, `A = M + 1`, `r = X mod M`, `s = X mod A`, and Euclidean quotient `K = X / M`:

```text
positive query:  (r - s) mod A =  K mod A
negative query:  (s - r) mod A = -K mod A
```

These congruences apply to arbitrary signed integers. An admitted quotient window selects an exact integer K when that is the requested result. K is a derived observable, not a persistent field.

The broader organizing criterion is exact observability: a requested result is recoverable from an observation precisely when it is constant on that observation's fibers. The supplied formal package develops constructive instances, coupled anchors, target transport, bounded divmod/GCD, and operation counts.

## Mock theta functions in the residue construction

Lean constructs the coefficients of all four functions in Ramanujan's original third-order group. Each summand has numerator $q^{n^2}$.

| Function | First index $n$ | Denominator of the $n$th summand |
|---|---:|---|
| $f(q)$ | 0 | $\prod_{j=1}^n(1+q^j)^2$ |
| $\phi(q)$ | 0 | $\prod_{j=1}^n(1+q^{2j})$ |
| $\psi(q)$ | 1 | $\prod_{j=1}^n(1-q^{2j-1})$ |
| $\chi(q)$ | 0 | $\prod_{j=1}^n(1-q^j+q^{2j})$ |

Each denominator has a unique formal reciprocal. Only summands with $n^2\le d$ can contribute to coefficient degree $d$. For each series $g$, the finite root theorem recovers $g_N(t\zeta)$ from the complete weighted residue packets at period $L$ when $\zeta^L=1$. The coupled-anchor theorem supplies such a period for a certified target root. [Formalization and source map](docs/reviews/2026-11-20-profinite-mock-theta-formalization.md)

Both fifth-order groups are formalized. For $i=0,1$, each of $f_i,\phi_i,\psi_i,\chi_i,F_i$ has a coefficient construction, a bound on its contributing summands, and a finite root evaluation using the coupled-anchor period. [Zero-subscript Lean source](formal/universal/MockThetaFifthZero.lean) · [One-subscript Lean source](formal/universal/MockThetaFifthOne.lean) · [Formulas and proof map](docs/reviews/2026-11-20-fifth-order-mock-theta.md)

The seventh-order module constructs $\mathcal F_0,\mathcal F_1,\mathcal F_2$ and proves finite evaluation for each. This completes coefficient and packet coverage for all seventeen original functions, across the groups of four, ten, and three. [Seventh-order Lean source](formal/universal/MockThetaSeventh.lean) · [Formulas, index conventions, and independent checks](docs/reviews/2026-11-20-seventh-order-mock-theta.md)

The four mock theta suites passed **32,866 exact assertions**, including independent coefficients of all seventeen functions through degree 40 and fourteen seventh-order Euler-product comparisons reaching degree 108. The even-order boundary values of the third-order $f$ are covered below.

The standalone Lean adapter pairs a signed NINE65 quotient and target readout with the finite packet evaluation for each of the four third-order functions. Its Lake project pins the two upstream revisions and includes executable examples for adjacent and other invertible anchors. [CRAMMockThetaBridge source and verification](adapters/CRAMMockThetaBridge/README.md)

## Partition rank, crank, and the shadow prime 11

The eleven partitions of six have one ordinary crank in each class modulo 11. Their rank histogram has empty bins at 4 and 7. Lean proves both results and exact integer criteria for uniform counts. It also proves that the coefficients of each seventh-order series can weight partition sizes in a finite crank character sum. Paired S8 readings evaluate that sum when each partition's crank supplies the signed increment in the specified transition. [Partition definitions](formal/universal/PartitionCrank11.lean) · [S6 and S8 readings](formal/universal/CrankShadow11.lean) · [Character and weighted pairing theorems](formal/universal/CrankCharacter11.lean) · [Formulas and examples](docs/reviews/2026-11-20-crank-shadow-eleven.md)

The crank and shadow suite passed **247 exact assertions**. [Crank execution log](evidence/current/profinite-mock-theta/crank-shadow-smoke.log)

## The analytic shadow of the third-order f

For $q=e^{2\pi i z}$, the holomorphic part of the normalized completion $M_f$ is $q^{-1}f(q^{24})$. Its weight-$3/2$ shadow is $4\sum_{m\equiv1\ (6)}m q^{m^2}$. Projecting the completion onto Fourier degrees $r$ modulo 11 projects its shadow onto degrees $-r$. Exactly five of the eleven projected completions have zero shadow. The review derives this result from Zwegers' completion and spells out what a CRAM degree observation supplies. [Formula, proof, and evidence](docs/reviews/2026-11-20-third-order-analytic-shadow.md) · [Exact Lean coefficients](formal/universal/MockThetaShadow.lean)

The Laurent normalization and unary theta coefficients passed **9,504 exact checks**. [Exact execution](evidence/current/profinite-mock-theta/third-order-shadow-smoke.log) · [Numerical evidence](evidence/current/analytic-shadow/README.md)

The separate Mathlib adapter compiles **45 explicitly declared theorems across six modules**. It proves the mod-11 projection law for the differential operator and evaluates it on finite completions built from the actual coefficients of $f$. Their derivatives converge to $4\Theta(z)$ throughout the upper half-plane. [Finite completion and its limiting derivative values](adapters/MockThetaAnalytic/ShadowMode.lean) · [Fourier projections](adapters/MockThetaAnalytic/ShadowProjection.lean) · [Analytic audit](adapters/MockThetaAnalytic/verification.json)

## Quantum radial limits of the rank and crank

At the cusp $-1$ the singular terms of $f(q)+b(q)$ cancel and leave 4. At $i$, the corrected function is $f(q)-b(q)$ and the value is $4i$. Folsom, Ono, and Rhoades prove both limits. At the eleventh root $w=\zeta=e^{2\pi i/11}$ their general rank/crank theorem gives $(1-\zeta)^2$ with compensating scalar $\zeta$. Lean proves the finite boundary formulas. A Mathlib theorem transfers FOR's limit to interior coefficient packet evaluations once the cutoffs approximate the Taylor series at each chosen radius. The review gives its hypotheses and Zagier's separate transformation criterion for quantum modularity. [Radial formulas and proof map](docs/reviews/2026-11-20-quantum-radial.md) · [Finite boundary formulas](formal/universal/QuantumRadial.lean) · [Analytic cutoff transfer](adapters/MockThetaAnalytic/QuantumRadialLimit.lean) · [Numerical evidence](evidence/current/quantum-radial/README.md)

At $w=1$, the same two-variable series gives the weight-$3/2$ quantum modular form proved by Bryson, Ono, Pitman, and Rhoades. Lean evaluates its terminating cusp sums and proves its translation law. At $x=1/11$, the finite inversion defect agrees with an independent eta period integral to better than $2\times10^{-61}$. [Known quantum form and source conventions](docs/reviews/2026-11-20-quantum-radial.md#a-quantum-modular-form-from-the-same-two-variable-series) · [Exact cusp construction](adapters/MockThetaAnalytic/QuantumStrange.lean)

The standard-library audit compiled **367 theorem declarations**. The six mock theta and radial suites plus the crank suite passed **44,196 exact assertions**, including 1,579 finite checks for the radial formulas. [Proof audit and execution](evidence/current/profinite-mock-theta/README.md)

## Read the project in four layers

| Layer | Purpose | Start here |
|---|---|---|
| Euclid's text | Edition-identified definitions and statements | [Text and derivation guide](docs/EUCLID_TO_CRAM.md) and the thesis appendices |
| Theory of the One | Consequences for units, compatible states, observation, exactness and composition | [Manuscript](foundations/theory_of_the_one/theory_of_the_one.md) and [foundations](docs/FOUNDATIONS.md) |
| Machine architecture | Configurable bases, typed operators, on-demand queries and source binding | [Architecture contract](docs/ARCHITECTURE.md) |
| Applications | Explicit bridges to NINE65, DSP, numerical methods and other systems | [Application map](docs/APPLICATIONS.md) |

This repository begins with the foundation and formal source package. Production engines are migrated only after their actual input/output contracts and dependencies are mapped.

## Evidence included

- [Arbitrary moduli and the profinite bridge — 20 November 2026](foundations/profinite_bridge/2026-11-20/README.md): both papers, editable sources, reproducible exact arithmetic, pinned source receipts, and the distinction between finite coefficient constructions and the proposed analytic correspondence.
- Editable thesis and its original figures and exact finite checker.
- Standalone Lean source package pinned to `leanprover/lean4:v4.27.0-rc1`.
- [Source reconciliation](docs/SOURCE_RECONCILIATION.md), publication hashes and separate historical/current evidence.

The [16 November 2026 deep review](docs/reviews/2026-11-16-deep-analysis.md) checked the complete 61-file source snapshot. Fresh pinned Lean verification passed all **130 theorem declarations**; the package build and **1,809 executable comparison/divmod/GCD pairs plus four controls** passed. The integer reference checker passed **821,881 assertions**. See [verification status](evidence/STATUS.md) and the [manuscript-to-Lean coverage map](docs/reviews/2026-11-16-formal-coverage.md) for the exact scope. These results cover the stated arithmetic contracts; application integration and performance have their own evidence requirements.

## Reproduce

Run the reference mathematics with Python 3.11 or newer:

```sh
python3 tools/run_reference_checks.py
```

With the pinned Lean/Lake installation available, reproduce the fresh proof audit, package build, and the executable smoke checks from the repository root:

```sh
python3 tools/verify_profinite_mock_theta.py --lean lean
```

The equivalent individual commands are:

```sh
cd formal/universal
python3 check_proofs.py --lean lean
lake build
lake env lean ClosureSmoke.lean
lake env lean MockThetaSmoke.lean
lake env lean FifthZeroSmoke.lean
lake env lean FifthOneSmoke.lean
lake env lean SeventhSmoke.lean
lake env lean MockThetaShadowSmoke.lean
lake env lean QuantumRadialSmoke.lean
lake env lean CrankShadowSmoke.lean
```

The standard-library checker rebuilds project imports in a fresh temporary directory. The smoke commands execute the concrete operations and independent coefficient oracles. The complex-analytic adapter has a separate Mathlib build and audit. [Analytic verification command](adapters/MockThetaAnalytic/README.md#reproduction) The latest receipts are under `evidence/current/profinite-mock-theta/`; the 16 November run remains under `evidence/current/lean/`, and supplied historical receipts remain under `evidence/historical/formal/`.

## Development contract

Read [AGENTS.md](AGENTS.md) before changing the project. Preserve integer-only internal arithmetic, authentic source/phase binding, on-demand K, declared observation boundaries, and separate scalar-compatible versus heterogeneous product-state semantics. Gates check current evidence and invariants; they must not require an earlier positive or negative conclusion to remain unchanged.

## Research lineage and rights

Euclid's account of units and measurement is the starting text of Theory of the One. The work develops consequences through explicit definitions and proofs, then realizes them in CRAM's representations and operators. Modern modular arithmetic, CRT and RNS research supply established mathematical context; see [sources](docs/SOURCES.md).

No new open-source license is selected by this publication. Preserve the authorship, citations and any existing license notices of imported material. Original research archives are held separately from this research core.
