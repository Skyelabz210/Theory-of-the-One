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
| [Numerical receipt](numerical.json) | Four FOR radial paths at 340 and 370 decimal digits, plus three BOPR cusp transformations at 45 and 65 decimal digits. The receipt records the two sets of assumptions, truncation bounds, precision comparisons and controls |
| [Numerical program](../../../tools/check_quantum_radial.py) | Independent evaluations of the interior rank and crank functions, the finite boundary value, and compensation sign or phase |

The even roots $-1$, $i$ and $e(1/6)$ use $t=1-1/d$ for
$d=50,100,200,400$. At $d=400$ the absolute distances to the predicted
limits $4$, $4i$ and $-4e(1/6)$ are about $0.00993$, $0.0521$ and $0.137$.
At $w=\zeta=e(1/11)$ the corresponding distances to $(1-\zeta)^2$ are about
$0.07096$, $0.04161$, $0.02298$, $0.01217$ for $d=200,400,800,1600$.
These are distances of interior samples to boundary values. The receipt
separately records arithmetic agreement between precisions and the effect
of changing the compensating phase.

At $x=1/11$, $-11$, and $1/2$, the BOPR checks evaluate the terminating
$U(1;e(x))$ and Kontsevich sums, the translated value, and the inversion
defect against an independent integral of Dedekind’s eta function. The largest
absolute discrepancy with the integral was below $2\times10^{-61}$ at 65
decimal digits. At $x=1/11$ using the opposite translation multiplier gives
error above 18. These are evaluations of a published weight-$3/2$ law on
rational cusps. [BOPR, Theorems 1.1 and 1.3](https://doi.org/10.1073/pnas.1211964109)

At the positive-angle roots of orders 34 and 10, FOR's compensated values
enter the weight-$1/2$ transformation of Folsom, Ki, Truong Vu and Yang.
The finite defect at the reflected cusps $-1/34$ and $-1/10$ differs from
the independently integrated theta period by about $1.065\times10^{-46}$.
The receipt records truncations, two quadrature orders, two working
precisions and branch and multiplier controls.
[Order-34 to order-10 derivation](../../../docs/reviews/2026-11-20-order-34-to-10.md)
· [Lean transport theorem](../../../adapters/MockThetaAnalytic/QuantumTransport34.lean)
· [Analytic kernel audit](../../../adapters/MockThetaAnalytic/verification.json)
· [Period computation](../../../tools/check_quantum_transport34.py)
· [Numerical receipt](transport34.json)

From the repository root, reproduce the finite proofs and exact checks with
the pinned Lean toolchain. Reproduce the numerical run with Python and
`mpmath==1.3.0`.

```sh
python3 tools/verify_profinite_mock_theta.py --lean lean
python3 tools/check_quantum_radial.py --dps 340 --receipt evidence/current/quantum-radial/numerical.json
python3 tools/check_quantum_transport34.py --receipt evidence/current/quantum-radial/transport34.json
```

The Mathlib adapter proves the interior Taylor identification for the signed coefficients of $f$. Its diagonal cutoff theorem for finite packets at any primitive even root uses FOR’s compensated radial limit as its analytic hypothesis. [Taylor identity and radial transfer](../../../adapters/MockThetaAnalytic/ThirdOrderTaylor.lean)
· [Kernel audit](../../../adapters/MockThetaAnalytic/verification.json)
