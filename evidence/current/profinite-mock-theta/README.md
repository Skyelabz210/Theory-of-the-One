# Exact mock theta coefficient bridge: execution receipts

The 20 November 2026 proof audit compiled **217 theorem declarations** with
`leanprover/lean4:v4.27.0-rc1` and its bundled standard library. The two
new modules account for 4 declarations in `CoefficientObservations` and 11 in
`MockThetaPhi`. Of the 217 declarations, 41 have empty axiom lists. The
remaining lists contain only `propext`, `Classical.choice`, and `Quot.sound`.
All four verification commands exited successfully without compiler warnings.

| File | Meaning |
|---|---|
| [execution.json](execution.json) | Commands, compiler binary hashes, source hashes, base revision, exit status, and executed smoke assertion count |
| [verification.json](verification.json) | Every compiled proof source, theorem, and transitive axiom dependency |
| [verification.log](verification.log) | Fresh temporary compilation and axiom-query output; no project oleans reused |
| [proof-audit.log](proof-audit.log) | Summary output from the proof checker |
| [lake-build.log](lake-build.log) | Package build using the registered module graph |
| [closure-smoke.log](closure-smoke.log) | Existing 1,809 concrete comparison/divmod/GCD pairs and four controls |
| [mock-theta-smoke.log](mock-theta-smoke.log) | 12,803 exact assertions across both coefficient series, their evaluations, and the joint Watson check |

The coefficient oracles calculate $f$ and $\phi$ over the integers through
degree 40, independently of Lean's formal division recurrence. The $f$ oracle
uses the coefficients $(-1)^k(k+1)$ at degree $jk$ of $(1+q^j)^{-2}$.
The $\phi$ oracle uses $(-1)^k$ at degree $2jk$ of $(1+q^{2j})^{-1}$. A joint check compares
the two named coefficient functions with Watson's identity in the integer
polynomial ring modulo $q^{41}$. The log reports coefficient tests, packet
and evaluation tests, and the joint identity separately.

The first implementation of $f$ at `853ed93` passed 202 theorem declarations
and 6,251 integer assertions in the mock theta smoke program. Its snapshot
records the source and compiler for that run. The current execution receipt
records the base commit and hashes of the files used in this run.
[First $f$ receipts](https://github.com/Skyelabz210/Theory-of-the-One/tree/853ed937d0fa3545683d668e72f6439b599529b5/evidence/current/profinite-mock-theta) · [Current execution](execution.json)

From the repository root, with the pinned Lean/Lake installation available:

```sh
python3 tools/verify_profinite_mock_theta.py --lean lean
```

Supply `--lean /path/to/the/pinned/bin/lean` when it is not on PATH. Lake must be
in the same installation. The runner first audits a fresh temporary proof build,
then builds the Lake package and executes both smoke modules. It invalidates
its previous receipt before a run and writes a failed execution receipt if a
check fails. Python 3.11 or newer suffices; no external Python dependencies or
Mathlib download are needed.

The [formalization review](../../../docs/reviews/2026-11-20-profinite-mock-theta-formalization.md)
states the exact mathematical scope. Topological duality, infinite analytic
evaluation, radial asymptotics, analytic shadows, and production observation
constructors are outside these receipts.
