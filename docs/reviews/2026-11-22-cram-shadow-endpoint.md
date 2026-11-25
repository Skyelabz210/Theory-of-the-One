# The S6 period at the starting cusp

At the starting cusp \(s=-1/24\), the kernel for Ramanujan’s recovered shadow has a square-root singularity at height zero. Lean proves that the raw cutoff integrals have two distinct constant subsequences there. Averaging two cutoffs from the same S6 prefix removes the oscillation. The averaged integrals converge uniformly for every real boundary parameter, and the full average already gives the exact terminating FKTY value at \(s\) from the prefix through degree \(852\). [S6 period construction](2026-11-22-cram-shadow-period.md) · [Endpoint proof](../../adapters/MockThetaAnalytic/ShadowEndpoint.lean)

## One prefix and two cutoffs

Let \(M_D=1+\lfloor\sqrt{24D+1}\rfloor\) be the number of available frequency slots from the degree-labeled readings of \(f\) modulo \(30030\). Write \(P_{D,N}^w(x)\) for the period of the first \(N\) slots, with \(N\le M_D\). The weight \(w\), with \(|w(r)|\le1\), multiplies the coefficient in sector \(-m^2\bmod11\). Set \(S=144\) for the full period and \(S=1584\) for a prime-11 sector or bounded combination. Recover
\[
A_D^w(x)=\tfrac12\left(P_{D,M_D-S}^w(x)+P_{D,M_D}^w(x)\right).
\]
The cutoff spacing is determined by the signed cusp phase. Both cutoffs use the coefficients recovered from one observed prefix. [Definition and cutoff coherence](../../adapters/MockThetaAnalytic/ShadowEndpoint.lean)

## Uniform control at the square-root singularity

For \(t>0\), the principal kernel obeys
\[
\left|\frac{i}{\sqrt{s-x+it}}\right|\le t^{-1/2}
\]
for every real \(x\). With \(a=\pi/12\), write \(g_m(t)=m e^{-am^2t}\) and \(C=\sqrt{\pi}/\sqrt a\). For \(m\ge S\) and \(m>0\), the integrals of the weighted differences satisfy
\[
\int_0^\infty \frac{|g_m-g_{m+S}|}{\sqrt t}\,dt
  \le \frac52 C\frac{S}{m},\qquad
\int_0^\infty \frac{|g_m-2g_{m+S}+g_{m+2S}|}{\sqrt t}\,dt
  \le \frac{51}{4}C\frac{S^2}{m^2}.
\]
These estimates follow from \(1-e^{-z}\le z\) for \(z\ge0\) and the three Gaussian moments of \(1,z,z^2\) with \(z=am^2t\). The two cutoffs absorb the unpaired edge of the original series. Shifting the remaining first differences once more leaves \(S\) first differences and an absolutely integrable series of second differences. Lean proves integrability for every \(x\) and the uniform bound
\[
|A_D^w(x)-P^w(x)|\le \frac{8C S^2}{M_D-S-1}
\]
when \(M_D-S\ge S\) and \(S\) is 144 or 1584 as above. [Gaussian estimates](../../adapters/MockThetaAnalytic/GaussianEndpoint.lean) · [Uniform limit and integrability](../../adapters/MockThetaAnalytic/ShadowEndpoint.lean)

## Exact value and raw cutoff control

At \(x=s\), integrating \(g_m(t)/\sqrt t\) gives \(C\) for every positive \(m\). Thus the raw period through slot \(N-1\) is \(2\,\mathrm{fktyScale}\) times the sum of the first \(N\) signed cusp phases. The full phase changes sign after 144 slots, so each complete block of 288 contributes zero. The coefficient cutoffs \(D_0=3456k^2\) and \(D_1=3456k^2+24k\), \(k\ge1\), give consecutive frequency cutoffs. Their raw results are respectively \(0\) and \(2\,\mathrm{fktyScale}\,e(-1/576)\), where \(e(z)=e^{2\pi iz}\). This gives the nonconvergence theorem. [Raw period and subsequences](../../adapters/MockThetaAnalytic/ShadowEndpoint.lean)

The average at the diagonal equals \(\mathrm{fktyScale}\) times a single initial half-block of signed phases. For the full period, the half-block and the 12 terminating FKTY terms at \(q=e(-1/24)\) reduce to the common representative
\[
4-4q+4q^2-4q^3+4q^6+4q^9+4q^{10}
\]
in \(\mathbb Z[q]/(q^{12}+1)\). The common normalization is \(\mathrm{fktyScale}\,e(-1/576)\). Lean identifies the diagonal period and every admissible full average with \(\phi_{\rm FKTY}(-1/24)\). A single prime-11 sector has an exact formula using its 1584-slot half-block. [Exact integer reduction](../../adapters/MockThetaAnalytic/ShadowEndpointValue24.lean) · [Sector formula](../../adapters/MockThetaAnalytic/ShadowEndpoint.lean)

## Replay

The replay generates 4,268 canonical S6 residues of \(f\) and checks six exact diagonal averages in the quotient. It verifies the distinct raw polynomials at \(D=3456,3480\) and checks that the eleven independently computed sector rows sum to the full row. Separate numerical quadrature checks 18 cutoff-and-parameter pairs. At \(-1/34\) and \(D=4267\), the measured error changes from \(1.2811\) to \(0.5288\) with cutoffs \(177\) and \(321\). The global proved upper bound is about \(3265.08\) at that prefix. The diagonal equality is exact, and the off-diagonal quadrature is checked by precision and order replication. [Replay program](../../adapters/MockThetaAnalytic/check_shadow_endpoint.py) · [Receipt](../../evidence/current/quantum-radial/shadow-endpoint.json)

Run from the repository root with the pinned Lean/Lake toolchain and `mpmath==1.3.0`.

    python3 adapters/MockThetaAnalytic/check_shadow_endpoint.py | diff -u evidence/current/quantum-radial/shadow-endpoint.json -
    (cd adapters/MockThetaAnalytic && python3 verify_analytic.py)
