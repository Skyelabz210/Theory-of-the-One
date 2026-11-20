# Universal exact-observation and K-Elimination package

Standalone CRAM observation proofs and the exact mock theta coefficient bridge. Pin: `leanprover/lean4:v4.27.0-rc1`. No Mathlib dependency.

The proof package covers coefficient construction, residue packets, cylinder
observation, and finite transforms for Ramanujan's third-order $f$ and $\phi$.
The execution receipt identifies the exact source and compiler, and the audit
lists the transitive axioms of every theorem.
[Formalization review](../../docs/reviews/2026-11-20-profinite-mock-theta-formalization.md)
· [Execution receipt](../../evidence/current/profinite-mock-theta/execution.json)
· [Proof audit](../../evidence/current/profinite-mock-theta/verification.json)

From the repository root, run the complete verification:

```sh
python3 tools/verify_profinite_mock_theta.py --lean lean
```

Alternatively, from this directory:

```sh
python3 check_proofs.py --lean lean
lake build
lake env lean ClosureSmoke.lean
lake env lean MockThetaSmoke.lean
```

The audit compiles project imports in a fresh temporary directory and checks
each theorem's dependencies against `propext`, `Classical.choice`, and
`Quot.sound`. The runner also builds the package and executes the two smoke
modules. `ClosureSmoke` covers 1,809 comparison/divmod/GCD pairs and four
controls. `MockThetaSmoke` checks both named coefficient sequences and a joint
Watson identity coefficientwise through degree 40.

| Module | Freshly checked theorem count |
|---|---:|
| ExactObservation | 9 |
| UniversalLift | 15 |
| RingReadout | 16 |
| IntegerSpecialization | 28 |
| CostedReadout | 7 |
| ReferenceChange | 3 |
| CoupledAnchors | 19 |
| ResidueAlgorithms | 6 |
| ResiduePrimitives | 14 |
| StarLift | 13 |
| ResidueSeries | 29 |
| ProfiniteObservations | 21 |
| CoefficientObservations | 4 |
| MockTheta | 22 |
| MockThetaPhi | 11 |
| **Total** | **217** |

The original compiler receipt and log are retained in `../../evidence/historical/formal/`. Read the root architecture contract before interpreting proof variables as runtime state.

## The mock theta connection

`MockTheta` defines the coefficients of $f$, whose denominator is
$\prod_{j=1}^n(1+q^j)^2$. `MockThetaPhi` uses the same binomial recurrence
once at each stride $2j$ to invert $\prod_{j=1}^n(1+q^{2j})$. The $q^{n^2}$
shift bounds the contributing summands at each coefficient degree.

`CoefficientObservations` combines the generic packets in `ResidueSeries`
with the compatible points and target admission in `ProfiniteObservations`.
The named theorems `mockTheta_from_coupled_anchors` and
`phi_from_coupled_anchors` specialize the finite root evaluation to each
series. The coupled anchors supply the admissible period through their
LCM/GCD resolution. Evaluation also requires the complete distribution of
coefficient packets at that period.

The selected primary is 30030. Topology, infinite analytic limits, and
harmonic-Maass shadows remain open in this package. The original $f$ audit
and the earlier 130-declaration audit retain their original execution records.
[First $f$ receipts](https://github.com/Skyelabz210/Theory-of-the-One/tree/853ed937d0fa3545683d668e72f6439b599529b5/evidence/current/profinite-mock-theta) · [16 November audit](../../evidence/current/lean/execution.json)

## What the checked package establishes

`ExactObservation` proves recoverability on the image of an observation and conditional semantic composition. `UniversalLift`, `RingReadout` and `IntegerSpecialization` construct the algebraic readouts. `CoupledAnchors` computes exact LCM/GCD ambiguity periods and target criteria. `StarLift` proves signed adjacent-anchor identities. `CostedReadout` counts operations in a declared expression language.

`ResiduePrimitives` discharges the abstract arithmetic obligations in `ResidueAlgorithms` using actual paired-residue operations. State has only main/anchor readings; winding is computed on demand. Concrete divmod and GCD are proved for natural inputs below the public frame capacity `M*A`; positive divisors may share factors with the observer moduli. Division uses repeated subtraction. Signed query theorems, nonunit-anchor readouts and the single-subtraction adjacent expression do not by themselves replace that concrete API or algorithm.

The [14-section manuscript coverage map](../../docs/reviews/2026-11-16-formal-coverage.md) identifies exact, partial and absent matches. Source binding, dynamic admission, full heterogeneous scheduling, and application-specific refinement belong to the integration work described in [the machine contract](../../docs/ARCHITECTURE.md).
