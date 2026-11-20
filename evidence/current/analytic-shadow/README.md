# Third-order analytic shadow evidence

The calculation evaluates the completion of Ramanujan's $f$ at three
upper-half-plane points. It compares the vertical integral and complementary
error function formulas, then independently estimates the differential operator
by finite differences in both real directions. All eleven projected derivatives
are checked at the first point. The expected shadow in this normalization is
$4\sum_{m\equiv1\ (6)}m q^{m^2}$.
[Mathematics and source conventions](../../../docs/reviews/2026-11-20-third-order-analytic-shadow.md)
· [Numerical receipt](numerical.json)
· [Exact coefficient audit](../profinite-mock-theta/verification.json)

With Python and `mpmath==1.3.0` installed, reproduce the 65-decimal-digit
calculation from the repository root.

```sh
python3 tools/check_analytic_shadow.py --dps 65 --receipt evidence/current/analytic-shadow/numerical.json
```

The receipt records the program hash, truncation and quadrature settings,
per-point discrepancies, step-halving checks, and controls for the sign,
dilation, and projection index. The analytic tail formulas are evaluated
numerically. Errors from quadrature, differencing, and roundoff are not
interval-certified. [Numerical checker](../../../tools/check_analytic_shadow.py)
