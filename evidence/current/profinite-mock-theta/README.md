# Exact mock theta coefficient bridge: execution receipts

The 20 November 2026 run used `leanprover/lean4:v4.27.0-rc1` and its bundled
standard library. It passed 202 theorem declarations, including 72 new ones,
with no compiler warnings, admitted proofs, or custom assumed declarations.
Forty declarations have no axiom dependencies. The rest use only `propext`,
`Classical.choice`, and `Quot.sound`.

| File | Meaning |
|---|---|
| [execution.json](execution.json) | Commands, compiler binary hashes, source hashes, base revision, exit status, and executed smoke assertion count |
| [verification.json](verification.json) | Every compiled proof source, theorem, and transitive axiom dependency |
| [verification.log](verification.log) | Fresh temporary compilation and axiom-query output; no project oleans reused |
| [proof-audit.log](proof-audit.log) | Summary output from the proof checker |
| [lake-build.log](lake-build.log) | Package build using the registered module graph |
| [closure-smoke.log](closure-smoke.log) | Existing 1,809 concrete comparison/divmod/GCD pairs and four controls |
| [mock-theta-smoke.log](mock-theta-smoke.log) | 6,251 exact assertions, including 41 independently calculated coefficients |

The named series is Ramanujan's third-order
`f(q) = sum q^(n*n)/product(1+q^j)^2`. The smoke oracle independently convolves
the explicit factor coefficients `(-1)^k*(k+1)` and applies the square shifts;
it does not use the formal division recurrence being checked. Empty
truncations, modulus one, signs, overlapping composite refinements, and the
root-period premise are exercised. Integer roots `1` and `-1` test finite
identities, with no complex convergence claim.

The source base revision is the preceding research archive. The working-source
hash manifest identifies the actual subsequently added and modified proof,
configuration, and runner files. The runner checks that those bytes do not
change during execution. Documentation edits after this run do not alter its
formal source snapshot.

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
