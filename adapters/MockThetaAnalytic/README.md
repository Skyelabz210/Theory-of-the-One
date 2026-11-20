# The third-order mock theta shadow and radial limits

The local core package supplies the integer `shadowWeight m`, equal to $m$ at $m\equiv1\pmod6$, $-m$ at $m\equiv5\pmod6$, and zero in the other four classes. This package interprets those signed coefficients over the complex numbers. [Core construction](../../formal/universal/MockThetaShadow.lean)

For $|u|<1$ the series $\Theta(u)=\sum_{m\ge0}\operatorname{shadowWeight}(m)u^{m^2}$ converges absolutely. The proof bounds each absolute term by $m|u|^m$. Summing eleven restrictions to $m^2\bmod11=r$ recovers the full series. Here $m$ indexes the magnitudes and $m^2$ is the Fourier degree tested in the projection. The nome $u=\exp(2\pi i\tau/24)$ lies in the open disk whenever $\operatorname{Im}\tau>0$. [Convergence and degree bins](ShadowConvergence.lean)

The normalized finite sum of eleven real translations acts as the residue-class indicator on each signed Laurent exponent. On the convergent shadow series in the integer-exponent variable $u=\exp(2\pi iz)$, the projection selects the corresponding sum above. The weight-$1/2$ differential operator $\xi$ conjugates scalar weights, sending a translation projection at $r$ to its partner at $-r$ under the stated real differentiability hypotheses. [Operator](ShadowOperator.lean) · [Monomials and series](ShadowProjection.lean)

The named function `mockCompletion` adds the infinite signed complementary-error-function correction to $Q^{-1}f(Q^{24})$ for $Q=e^{2\pi iz}$. Lean proves that the hypergeometric series is holomorphic in the disk. A common summable bound on the correction modes and their first real derivatives on each $\operatorname{Im}(z)\ge a>0$ permits differentiating the entire sum. For every $\operatorname{Im}(z)>0$, `xiHalf_mockCompletion` then gives $\xi_{1/2}M_f=4\Theta$, and the projected identity selects four times the unary bin at $-r$. Exactly $r=1,3,4,5,9$ have identically zero projected shadow. [Holomorphic part](MockHolomorphic.lean) · [Gaussian tail](ShadowGaussian.lean) · [Mode bounds](ShadowBounds.lean) · [Infinite differentiation](ShadowInfinite.lean) · [Sector support](ShadowSectors.lean) · [Completion and projections](MockCompletion.lean)

The finite mode calculation and its pointwise limit remain available for every pair of cutoffs. The comparison of the Fourier normalization with Zwegers' integral and the modular transformation of the completed vector are recorded in the review. [Finite modes](ShadowMode.lean) · [Normalization and literature](../../docs/reviews/2026-11-20-third-order-analytic-shadow.md)

A separate radial theorem handles the original $f$ coefficients at a primitive even root. Given the interior Taylor expansion and the compensated radial limit of Folsom–Ono–Rhoades, it constructs cutoffs growing with the radial sequence. Every choice of truncations beyond those cutoffs has the same compensated limit. [Radial transfer](QuantumRadialLimit.lean)

The $w=1$ specialization of the finite $U$-polynomial gives a second cusp function. At every rational $x=a/K$ with positive $K$, its partial sum stabilizes when the cutoff reaches $K$, so the infinite Pochhammer series has exactly that finite sum. Translation by $1$ multiplies its normalized value by $e(-1/24)$, where $e(z)=\exp(2\pi iz)$. At $x=1/2$ the exact value is $3e(-1/48)$. At $x=1/11$ the proof reduces the normalized value to an explicit polynomial in $e(1/11)$. [Finite strange series and cusp values](QuantumStrange.lean)

## Reproduction

With Git, Python 3.11 or newer and the pinned Lean/Lake installation on `PATH`, run from the repository root

```sh
cd adapters/MockThetaAnalytic
python3 verify_analytic.py
```

Lake reads `../../formal/universal` from the same checkout. The committed manifest fixes Mathlib and its transitive dependencies. An initial build needs network access for the Git checkouts and can compile the imported Mathlib modules from source. Subsequent runs reuse those dependency builds and rebuild the local analytic modules. The verifier checks the Lean environment for transitive axiom dependencies, checks public results by name and records source hashes for the analytic modules and their imported core sources. Generated logs and `receipt.json` are written to `.lake/verification/`. [Pinned dependencies](lake-manifest.json) · [Kernel audit](AnalyticAudit.lean) · [Recorded run](verification.json)
