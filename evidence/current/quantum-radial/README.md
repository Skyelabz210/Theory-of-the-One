# Quantum radial limits of the rank and crank

The exact Lean suite checks terminating boundary polynomials in finite fields.
A separate complex numerical calculation evaluates the rank series and the
compensating crank function at interior points approaching each selected cusp.
FOR's Theorems 1.1 and 1.2 identify their radial limits.
[Formulas, admissible roots, and limits](../../../docs/reviews/2026-11-20-quantum-radial.md)
· [FOR, Theorems 1.1 and 1.2](https://afolsom.people.amherst.edu/FolsomOnoRhoades-ForumPi.pdf#page=4)

| Evidence | Extent |
|---|---|
| [Exact Lean proof](../../../formal/universal/QuantumRadial.lean) | Finite stabilization, degree packets, coupled-anchor evaluation, and the diagonal rank/crank right side |
| [Exact execution](../profinite-mock-theta/quantum-radial-smoke.log) | 1,579 assertions. The finite-field checks cover all primitive roots of orders 2, 4, 6, 8, 10, and 22 in the field of 1,321 elements and an order-11 fixture in the field of 727 elements |
| [Numerical receipt](numerical.json) | Four radial paths, repeated at 340 and 370 decimal digits. The record gives the two interior function values, their corrected difference, analytic tail estimates, precision comparisons, and controls |
| [Numerical program](../../../tools/check_quantum_radial.py) | Independent evaluations of the interior rank and crank functions, the finite boundary value, and compensation sign or phase |

The even roots $-1$, $i$ and $e(1/6)$ use $t=1-1/d$ for
$d=50,100,200,400$. At $d=400$ the absolute distances to the predicted
limits $4$, $4i$ and $-4e(1/6)$ are about $0.00993$, $0.0521$ and $0.137$.
At $w=\zeta=e(1/11)$ the corresponding distances to $(1-\zeta)^2$ are about
$0.07096$, $0.04161$, $0.02298$, $0.01217$ for $d=200,400,800,1600$.
These are distances of interior samples to boundary values. The receipt
separately records arithmetic agreement between precisions and the effect
of changing the compensating phase.

From the repository root, reproduce the finite proofs and exact checks with
the pinned Lean toolchain. Reproduce the numerical run with Python and
`mpmath==1.3.0`.

```sh
python3 tools/verify_profinite_mock_theta.py --lean lean
python3 tools/check_quantum_radial.py --dps 340 --receipt evidence/current/quantum-radial/numerical.json
```
