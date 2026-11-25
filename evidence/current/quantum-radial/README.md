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
precisions and branch and multiplier controls. Lean also derives this exact
identity from the two cusp limits and the theta transformation.
[Order-34 to order-10 derivation](../../../docs/reviews/2026-11-20-order-34-to-10.md)
· [Exact period identity](../../../adapters/MockThetaAnalytic/EichlerBridge.lean)
· [Analytic kernel audit](../../../adapters/MockThetaAnalytic/verification.json)
· [Period computation](../../../tools/check_quantum_transport34.py)
· [Numerical receipt](transport34.json)

The S6 prefix replay reconstructs the theta coefficients of the same period and integrates their finite polynomial. Eight cutoffs and three real parameters exercise the endpoint error theorem. The infinite reference uses Poisson summation, with a second check from the finite cusp defect at \(-1/34\). The receipt records exact phase-shift controls and the error at every cutoff. [Period recovery and theorem](../../../docs/reviews/2026-11-22-cram-shadow-period.md) · [S6 period receipt](shadow-period.json)

The two-cutoff average is checked exactly at \(-1/24\) by reducing the observed phase sums and the terminating FKTY series to integer polynomials modulo \(q^{12}+1\). The replay includes the two raw cutoff controls and numerical comparisons on both sides of the cusp. [Endpoint theorem and derivation](../../../docs/reviews/2026-11-22-cram-shadow-endpoint.md) · [Endpoint receipt](shadow-endpoint.json)

At $\zeta=e^{2\pi i/34}$, independent evaluations of the defining $f$, the product $b$ and the third-order $\phi(-q)$ check the disk cancellation. For radii $0.999$, $0.9998$, $0.99995$ and $0.99999$, the distances of $f+b$ to the finite boundary are approximately $2.50$, $0.755$, $0.214$ and $0.0445$. At the last radius the opposite compensation sign gives a distance of $1.71\times10^{64}$. The receipt records both precisions and the separate truncation bounds. [Watson calculation](../../../tools/check_watson_radial34.py) · [Numerical receipt](watson34.json) · [Lean radial theorem](../../../adapters/MockThetaAnalytic/FOROrder34.lean)

At every primitive order-24 root, Lean proves the radial limit of $f-b$ from the complementary identity with $\psi(-q)$. The replay checks the exact finite value and an entire period of signed mod-8 readouts, including the mod-4 sign alias. It samples the radial approach at six radii per root and checks the defining $f$ series and $b$ product independently at two radii per root. [Order-24 proof and replay](../../../docs/reviews/2026-11-22-cram-order24.md) · [Execution receipt](watson24.json)

The uniform Watson-to-FOR identity and radial proof cover every primitive even root. The independent integer replay performs 44 divisions by \(X^k+1\) and 45 additional divisions by \(X^s+1\) for odd \(s\) dividing even \(k\). For \(1\le k\le44\), it checks the quadratic coefficients at all 22 odd indices and measures root multiplicity at \(-1\) for 200 half-period and prime pairs. Modulo 11 it finds 38 simple roots, two double roots, and four roots of multiplicity 11. The replay also checks the cleared identity for every even order through 192, the opposite denominator parity, the imprimitive control, and signed phase comparisons. [Universal congruences](../../../adapters/MockThetaAnalytic/FORWatsonCongruence.lean) · [Multiplicity theorem](../../../adapters/MockThetaAnalytic/FORWatsonMultiplicity.lean) · [Exact replay receipt](watson-even-roots.json)

From the repository root, reproduce the finite proofs and exact checks with
the pinned Lean toolchain. Reproduce the numerical run with Python and
`mpmath==1.3.0`.

```sh
python3 tools/verify_profinite_mock_theta.py --lean lean
python3 tools/check_quantum_radial.py --dps 340 --receipt evidence/current/quantum-radial/numerical.json
python3 tools/check_quantum_transport34.py --receipt evidence/current/quantum-radial/transport34.json
python3 adapters/MockThetaAnalytic/check_shadow_period.py | diff -u evidence/current/quantum-radial/shadow-period.json -
python3 adapters/MockThetaAnalytic/check_shadow_endpoint.py | diff -u evidence/current/quantum-radial/shadow-endpoint.json -
python3 tools/check_watson_radial34.py --receipt evidence/current/quantum-radial/watson34.json
python3 tools/check_watson_radial24.py | diff -u evidence/current/quantum-radial/watson24.json -
python3 tools/check_watson_even_roots.py | diff -u evidence/current/quantum-radial/watson-even-roots.json -
```

The Mathlib adapter proves the interior Taylor identification for the signed coefficients of $f$. The diagonal cutoff theorem supplies compensated packet convergence at every primitive even root and the normalized FKTY value at its reflected rational cusp. The integer Watson certificate holds in the full quotient by $X^k+1$ for every positive $k$. [Even-order packet theorem](../../../adapters/MockThetaAnalytic/FOREvenRoot.lean) · [Uniform certificate](../../../adapters/MockThetaAnalytic/FORWatsonQuotient.lean) · [Kernel audit](../../../adapters/MockThetaAnalytic/verification.json)
