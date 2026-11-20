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

The two series formalized here belong to Ramanujan's original third-order family.

$$
f(q)=\sum_{n\ge0}\frac{q^{n^2}}{\prod_{j=1}^{n}(1+q^j)^2},
\qquad
\phi(q)=\sum_{n\ge0}\frac{q^{n^2}}{\prod_{j=1}^{n}(1+q^{2j})}.
$$

Each denominator has a unique formal reciprocal, and only summands with $n^2\le d$ can contribute at degree $d$. For either series $g$, its degree truncation $g_N(t\zeta)$ is recovered by weighting the complete set of residue packets at an admitted period $L$ with $\zeta^L=1$. The coupled-anchor theorem supplies such a period for a certified target root. [Formalization and source map](docs/reviews/2026-11-20-profinite-mock-theta-formalization.md)

The audit passed **217 theorem declarations**. The mock theta smoke run passed **12,803 exact assertions**, including independent integer coefficients for both series and a joint check of Watson's identity through degree 40. The infinite analytic transform and radial asymptotics remain open here. [Execution receipts](evidence/current/profinite-mock-theta/README.md)

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

With the pinned Lean/Lake installation available, reproduce the fresh proof audit, package build, and both executable smoke checks from the repository root:

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
```

The checker rebuilds project imports in a fresh temporary directory. The smoke commands execute the concrete operations and independent coefficient oracles; neither the proof checker nor the default Lake target runs them automatically. No Mathlib dependency is required. The latest receipts are under `evidence/current/profinite-mock-theta/`; the 16 November run remains under `evidence/current/lean/`, and supplied historical receipts remain under `evidence/historical/formal/`.

## Development contract

Read [AGENTS.md](AGENTS.md) before changing the project. Preserve integer-only internal arithmetic, authentic source/phase binding, on-demand K, declared observation boundaries, and separate scalar-compatible versus heterogeneous product-state semantics. Gates check current evidence and invariants; they must not require an earlier positive or negative conclusion to remain unchanged.

## Research lineage and rights

Euclid's account of units and measurement is the starting text of Theory of the One. The work develops consequences through explicit definitions and proofs, then realizes them in CRAM's representations and operators. Modern modular arithmetic, CRT and RNS research supply established mathematical context; see [sources](docs/SOURCES.md).

No new open-source license is selected by this publication. Preserve the authorship, citations and any existing license notices of imported material. Original research archives are held separately from this research core.
