# Universal exact-observation and K-Elimination package

Source imported unchanged from the supplied CRAM proof bundle. Pin: `leanprover/lean4:v4.27.0-rc1`. No Mathlib dependency.

The imported historical receipt reports 130 theorem declarations across ten substantive modules plus the umbrella import module. This seed verified every module hash against that receipt. It did not rerun the compiler because the pinned Lean toolchain is not installed in this session.

```sh
python3 check_proofs.py --lean lean
```

The audit compiles each project import in a fresh temporary directory and checks transitive axioms. The standard foundational axioms admitted by this audit are `propext`, `Classical.choice` and `Quot.sound`; the historical receipt reports 30 declarations with no axiom dependencies. Do not describe the whole package as axiom-free.

| Module | Historical theorem count |
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
