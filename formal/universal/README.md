# Universal exact-observation and K-Elimination package

Lean modules imported unchanged from the supplied CRAM proof bundle. Pin: `leanprover/lean4:v4.27.0-rc1`. No Mathlib dependency. The review changes the Python checker's receipt invalidation, not the theorem sources.

On 16 November 2026 the pinned compiler was installed and the sources were freshly checked: **130 theorem declarations passed** across ten substantive modules plus the umbrella import module. All eleven proof-module sources remain unchanged from the imported bundle and match the historical receipt. Current logs and source hashes are in [fresh verification](../../evidence/current/lean/verification.json) and [execution metadata](../../evidence/current/lean/execution.json).

```sh
python3 check_proofs.py --lean lean
lake build
lake env lean ClosureSmoke.lean
```

The audit compiles each project import in a fresh temporary directory and checks transitive axioms. The standard foundational axioms admitted by this audit are `propext`, `Classical.choice` and `Quot.sound`; the fresh receipt records 30 declarations with no axiom dependencies. Do not describe the whole package as axiom-free.

The separate Lake build passed 13 jobs. `ClosureSmoke.lean` executed 1,809 comparison/divmod/GCD pairs plus four boundary/refusal controls. The default build target and `check_proofs.py` do not automatically run that smoke module; all three commands are required to reproduce this review's formal and executable checks.

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

The original compiler receipt and log are retained in `../../evidence/historical/formal/`. Read the root architecture contract before interpreting proof variables as runtime state.

## What the checked package establishes

`ExactObservation` proves recoverability on the image of an observation and conditional semantic composition. `UniversalLift`, `RingReadout` and `IntegerSpecialization` construct the algebraic readouts. `CoupledAnchors` computes exact LCM/GCD ambiguity periods and target criteria. `StarLift` proves signed adjacent-anchor identities. `CostedReadout` counts operations in a declared expression language.

`ResiduePrimitives` discharges the abstract arithmetic obligations in `ResidueAlgorithms` using actual paired-residue operations. State has only main/anchor readings; winding is computed on demand. Concrete divmod and GCD are proved for natural inputs below the public frame capacity `M*A`; positive divisors may share factors with the observer moduli. Division uses repeated subtraction. Signed query theorems, nonunit-anchor readouts and the single-subtraction adjacent expression do not by themselves replace that concrete API or algorithm.

The [14-section manuscript coverage map](../../docs/reviews/2026-11-16-formal-coverage.md) identifies exact, partial and absent matches. Source binding, dynamic admission, full heterogeneous scheduling, and application-specific refinement belong to the integration work described in [the machine contract](../../docs/ARCHITECTURE.md).
