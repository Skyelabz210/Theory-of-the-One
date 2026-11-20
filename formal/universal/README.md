# Universal exact-observation and K-Elimination package

Standalone CRAM observation proofs and the exact mock theta coefficient bridge. Pin: `leanprover/lean4:v4.27.0-rc1`. No Mathlib dependency.

On 20 November 2026 a fresh temporary build and transitive axiom audit passed **202 theorem declarations**: the original 130 declarations plus 72 in the new `ResidueSeries`, `ProfiniteObservations`, and `MockTheta` modules. The ten original substantive proof modules remain unchanged. The umbrella module, Lake roots, and audit module list now include the three new modules. The [formalization review](../../docs/reviews/2026-11-20-profinite-mock-theta-formalization.md) maps the definitions and theorems to their mathematical claims.

The [execution receipt](../../evidence/current/profinite-mock-theta/execution.json) records actual commands, compiler and source hashes, and smoke results. The [proof receipt](../../evidence/current/profinite-mock-theta/verification.json) records every theorem and its axioms. The prior 16 November 130-declaration audit remains in [its dated execution record](../../evidence/current/lean/execution.json).

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

The audit compiles each project import in a fresh temporary directory and checks transitive axioms. The standard foundational axioms admitted by this audit are `propext`, `Classical.choice` and `Quot.sound`; the fresh receipt records 40 declarations with no axiom dependencies. The entire package is not axiom-free. The audit rejects missing or duplicate axiom queries, warnings, admitted proofs, and custom assumed declarations.

The separate Lake build passed. `ClosureSmoke.lean` executed 1,809 comparison/divmod/GCD pairs plus four boundary/refusal controls. `MockThetaSmoke.lean` passed 6,251 exact assertions, including 41 coefficients independently calculated by finite polynomial convolution, packet refinement, and finite root evaluation. The default build target and `check_proofs.py` do not automatically run either smoke module; the reproduction runner executes all four commands.

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
| MockTheta | 22 |
| **Total** | **202** |

The original compiler receipt and log are retained in `../../evidence/historical/formal/`. Read the root architecture contract before interpreting proof variables as runtime state.

## The mock theta connection

`MockTheta` constructs the coefficients of Ramanujan's third-order
$f(q)=\sum_{n\ge0}q^{n^2}/(-q;q)_n^2$. Triangular formal division has a proved inverse law and uniqueness; coefficient support proves that the summand cutoff stabilizes at each degree. These definitions instantiate `ResidueSeries` coefficient packets, finite weighted pushforwards, and root evaluation.

`ProfiniteObservations` supplies algebraic inverse-system tuple data, diagonal points, cylinder functions, and exact target recoverability. `mockCylinder` and `mockWeightedCylinder` put the named coefficients into that tuple construction. The final `mockTheta_from_coupled_anchors` theorem composes the existing anchor observation criterion with the finite transform through the exact LCM/GCD period. Arbitrary admission families enforce precisely their declared divisibility transitions; full compatibility between incomparable moduli requires connecting coordinates.

The selected primary is fixed at 30030. Semantic quotient variables in proofs do not become stored state. The full coefficient distribution needed by a finite transform is separate from an observed residue of one runtime source. Topology, continuity, Pontryagin duality, infinite analytic limits, harmonic-Maass shadows, and the other sixteen original named functions are beyond this initial formal slice.

## What the checked package establishes

`ExactObservation` proves recoverability on the image of an observation and conditional semantic composition. `UniversalLift`, `RingReadout` and `IntegerSpecialization` construct the algebraic readouts. `CoupledAnchors` computes exact LCM/GCD ambiguity periods and target criteria. `StarLift` proves signed adjacent-anchor identities. `CostedReadout` counts operations in a declared expression language.

`ResiduePrimitives` discharges the abstract arithmetic obligations in `ResidueAlgorithms` using actual paired-residue operations. State has only main/anchor readings; winding is computed on demand. Concrete divmod and GCD are proved for natural inputs below the public frame capacity `M*A`; positive divisors may share factors with the observer moduli. Division uses repeated subtraction. Signed query theorems, nonunit-anchor readouts and the single-subtraction adjacent expression do not by themselves replace that concrete API or algorithm.

The [14-section manuscript coverage map](../../docs/reviews/2026-11-16-formal-coverage.md) identifies exact, partial and absent matches. Source binding, dynamic admission, full heterogeneous scheduling, and application-specific refinement belong to the integration work described in [the machine contract](../../docs/ARCHITECTURE.md).
