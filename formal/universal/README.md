# Universal exact-observation and K-Elimination package

Standalone CRAM observation proofs and the exact mock theta coefficient bridge. Pin: `leanprover/lean4:v4.27.0-rc1`. No Mathlib dependency.

The proof package covers coefficient construction, residue packets, cylinder
observation, and finite transforms for the four original third-order series
and all ten fifth-order and three seventh-order series in the original list.
The execution receipt identifies the exact source and compiler, and the audit
lists the transitive axioms of every theorem.
[Formalization review](../../docs/reviews/2026-11-20-profinite-mock-theta-formalization.md)
· [Seventh-order constructions](../../docs/reviews/2026-11-20-seventh-order-mock-theta.md)
· [Fifth-order constructions](../../docs/reviews/2026-11-20-fifth-order-mock-theta.md)
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
lake env lean FifthZeroSmoke.lean
lake env lean FifthOneSmoke.lean
lake env lean SeventhSmoke.lean
```

The audit compiles project imports in a fresh temporary directory and checks
each theorem's dependencies against `propext`, `Classical.choice`, and
`Quot.sound`. The runner also builds the package and executes the smoke
modules. `ClosureSmoke` covers 1,809 comparison/divmod/GCD pairs and four
controls. `MockThetaSmoke` checks all four third-order coefficient sequences and three
relations from Watson through degree 40. `FifthZeroSmoke` covers the five
zero-subscript series and checks the relations in Ramanujan's letter at the same degrees.
`FifthOneSmoke` covers the five one-subscript series, their two initial
geometric summands, and Watson's shifted relation through degree 41.
`SeventhSmoke` verifies the three seventh-order sequences through degree 40,
checks their cutoffs, and tests Garvan's Euler-weighted relations.

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
| MockTheta | 24 |
| MockThetaPhi | 11 |
| MockThetaPsi | 14 |
| MockThetaChi | 14 |
| FifthOrderSeries | 7 |
| MockThetaFifthZero | 13 |
| MockThetaFifthOne | 15 |
| MockThetaSeventh | 17 |
| **Total** | **299** |

The original compiler receipt and log are retained in `../../evidence/historical/formal/`. Read the root architecture contract before interpreting proof variables as runtime state.

## The mock theta connection

`MockTheta` constructs $f$ from the squared factors $\prod_{j=1}^n(1+q^j)^2$.
`MockThetaPhi` uses binomial division at each even stride $2j$ with sign
$+1$. `MockThetaPsi` starts at $n=1$ and divides by $1-q^{2j-1}$.
`MockThetaChi` proves the coefficient action of
$(1-x+x^2)(1+x)=1+x^3$ and uses it to divide by each trinomial at $x=q^j$.
For all four series, `squareSum_stable` and the named support theorems
show that indices $n<K$ suffice at degree $d<K^2$.

`CoefficientObservations` combines `ResidueSeries` packets with the
compatible points and target admission in `ProfiniteObservations`.
Each series has a named finite root evaluation. The anchor specializations
are `mockTheta_from_coupled_anchors`, `phi_from_coupled_anchors`,
`psi_from_coupled_anchors`, and `chi_from_coupled_anchors`. The anchors
supply the period through their LCM/GCD resolution. Evaluation uses the
complete distribution of coefficient packets at that period.

The selected primary is 30030. Topology, infinite analytic limits, and
harmonic-Maass shadows remain open here. The seventh-order constructions complete the original
seventeen named series. Earlier
source and execution records are available for each proof package.
[First $f$ receipts](https://github.com/Skyelabz210/Theory-of-the-One/tree/853ed937d0fa3545683d668e72f6439b599529b5/evidence/current/profinite-mock-theta) · [$f$, $\phi$ receipts](https://github.com/Skyelabz210/Theory-of-the-One/tree/769b724802ba1fd2e042718ac2dbc95b79d6fed1/evidence/current/profinite-mock-theta)
· [Zero-subscript checkpoint](https://github.com/Skyelabz210/Theory-of-the-One/blob/a028a794b0eccdac35281b09dae825455d0ea73e/evidence/current/profinite-mock-theta/execution.json)
· [16 November audit](../../evidence/current/lean/execution.json)

## What the checked package establishes

`ExactObservation` proves recoverability on the image of an observation and conditional semantic composition. `UniversalLift`, `RingReadout` and `IntegerSpecialization` construct the algebraic readouts. `CoupledAnchors` computes exact LCM/GCD ambiguity periods and target criteria. `StarLift` proves signed adjacent-anchor identities. `CostedReadout` counts operations in a declared expression language.

`ResiduePrimitives` discharges the abstract arithmetic obligations in `ResidueAlgorithms` using actual paired-residue operations. State has only main/anchor readings; winding is computed on demand. Concrete divmod and GCD are proved for natural inputs below the public frame capacity `M*A`; positive divisors may share factors with the observer moduli. Division uses repeated subtraction. Signed query theorems, nonunit-anchor readouts and the single-subtraction adjacent expression do not by themselves replace that concrete API or algorithm.

The [14-section manuscript coverage map](../../docs/reviews/2026-11-16-formal-coverage.md) identifies exact, partial and absent matches. Source binding, dynamic admission, full heterogeneous scheduling, and application-specific refinement belong to the integration work described in [the machine contract](../../docs/ARCHITECTURE.md).
