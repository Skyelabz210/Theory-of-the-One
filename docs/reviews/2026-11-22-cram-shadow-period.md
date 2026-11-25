# Recovering the FKTY boundary period from S6

The degree-labeled residues of Ramanujan’s \(f\) modulo \(30030\) determine a finite shadow polynomial. Its integral along the **whole open cusp ray** converges to the period in the order‑34 to order‑10 quantum transformation. The same construction applies to each prime‑11 sector. Lean proves the convergence and a cutoff-dependent error bound. [S6 coefficient reconstruction](2026-11-21-cram-shadow-reconstruction.md) · [Period proof](../../adapters/MockThetaAnalytic/ShadowPeriod.lean)

## The polynomial and its period

Write \(e(z)=e^{2\pi i z}\), \(s=-1/24\), and \(N_D=1+\lfloor\sqrt{24D+1}\rfloor\). Let \(A_D(m)\) be the recovered differential-shadow coefficient at degree \(m^2\) from the prefix through mock degree \(D\). For any weights \(w\) on the prime‑11 labels with \(|w(r)|\le1\), define
\[
\Theta_D^{w}(u)=\frac12\sum_{m<N_D}w(-m^2\bmod11)A_D(m)e(m^2u/24),
\qquad
P_D^w(x)=\int_0^\infty\frac{i\,\Theta_D^w(s+it)}{\sqrt{s-x+it}}\,dt .
\]
The factor \(1/2\) converts the differential shadow to the FKTY bilateral normalization. An indicator weight selects the previously proved sector polynomial, and the infinite numerator on \(t>0\) is then \(\xi_{1/2}(P_r M_f)((s+it)/24)/2\). All weights equal to one give the FKTY theta period. [Finite polynomial and sector identification](../../adapters/MockThetaAnalytic/ShadowPeriod.lean)

## Error up to the endpoint

Put \(a=\pi/12\) and \(g_m(t)=m e^{-a m^2t}\). The signed cusp phase of \(g_m\) reverses after \(144\) modes. To preserve a prime‑11 label while reversing the sign, use \(S=1584=11\cdot144\), since \(1584\equiv0\pmod{11}\). A single \(144\)-mode shift sends \(m=1\) from sector \(10\) to sector \(7\). Use \(S=144\) for the full period and \(S=1584\) for an individual sector or a bounded combination. [Cusp phase at \(s\)](../../adapters/MockThetaAnalytic/FKTYCuspModes.lean) · [Sector shift and control](../../adapters/MockThetaAnalytic/ShadowPeriod.lean)

For the omitted tail starting at \(N_D\), shifting the series once expresses the difference between the infinite and finite numerators as a finite edge of \(S\) modes plus phase-weighted differences \(g_m-g_{m+S}\). The single-mode integral on the edge is \(1/(am)\). The absolute integral of each paired difference is at most \(3S/(am^2)\). Lean sums the squares by comparison with \(1/(m-1)-1/m\), and bounds the kernel by \(\delta^{-1/2}\) on \(|s-x|\ge\delta>0\). This yields
\[
\left|P_D^w(x)-P^w(x)\right|
\le
\frac{4S}{a\sqrt{\delta}\,(N_D-1)} .
\]
The convergence is uniform on this entire set of real \(x\). Absolute integration of the individual Gaussian modes gives a harmonic series on the nonzero support. Pairing supplies the summable square tail before taking norms. The finite approximation integrates the original truncated polynomial. [Gaussian difference bound](../../adapters/MockThetaAnalytic/GaussianPairIntegrable.lean) · [Error and uniform limit](../../adapters/MockThetaAnalytic/ShadowPeriod.lean)

At equality \(x=s\), the averaged cutoff theorem uses the integrable second-difference tail and identifies the exact terminating cusp value. [Starting cusp and two-cutoff average](2026-11-22-cram-shadow-endpoint.md)

## The order‑34 boundary value

At \(x=-1/34\), the separation is \(5/408\). Lean identifies the limit of \(P_D^1(-1/34)\) with the exact normalized packet defect for any signed source and stabilized cutoffs \(N_{34}\ge17\) and \(N_{10}\ge5\). Substituting this period into the existing transport identity gives a second convergence theorem for the order‑34 compensated boundary value. Its inputs are the S6 coefficient prefix and the finite order‑10 endpoint. When forming the translated order‑34 packets for an arbitrary signed source, the existing character readout also uses that source’s mod‑17 anchor. [Normalized period and boundary limit](../../adapters/MockThetaAnalytic/ShadowPeriod.lean) · [Source-bound character readout](../../adapters/MockThetaAnalytic/Order34Source.lean)

### A certified cutoff for the translated endpoint

Let \(T_{10}(X)\) and \(T_{34}(X)\) be the complete translated packet values at periods \(30030\) and \(510510\), with \(N_{10}\ge5\) and \(N_{34}\ge17\). For \(b=10,34\), write \(\beta_b=e((X\bmod b)/b)\) and \(c_b=\mathrm{fktyScale}\,e(-1/(24b))\). The implementation reads \(\beta_{10}\) from parity and mod 5 and \(\beta_{34}\) from parity and mod 17. For the authentic degree-labeled prefix of \(f\) through \(D\), Lean proves for every signed \(X\) that
\[
\widehat T_{34,D}=\frac{\beta_{34}}{c_{34}}
  \left(P_D^1(-1/34)+\sqrt{17/5}\,c_{10}\frac{T_{10}(X)}{\beta_{10}}\right),
\qquad
\left|\widehat T_{34,D}-T_{34}(X)\right|
\le \frac{7680}{\lfloor\sqrt{24D+1}\rfloor}.
\]
The constant follows from \(5/408\ge1/100\), \(\pi/12\ge1/4\), and \(|c_{34}|=\sqrt{12}\ge3\). Restoring the observed phase preserves the error norm. The \(D=0\) prefix already gives a defined estimate. [Finite estimate and proof](../../adapters/MockThetaAnalytic/ShadowPeriod.lean)

For a positive rational tolerance \(a/b\), take \(n=\lceil b/a\rceil\) and any \(D\ge2{,}457{,}600n^2\). Then \(\lfloor\sqrt{24D+1}\rfloor\ge7680n\) and the error is at most \(1/n\le a/b\). Degree is inclusive, so the guarantee for tolerance \(1\) uses \(2{,}457{,}601\) readings. This certificate bounds truncation of the exact integral of the recovered finite polynomial. Floating-point evaluation of that integral has its own numerical error. [Precision theorems](../../adapters/MockThetaAnalytic/ShadowPeriod.lean) · [Typed checks](../../adapters/MockThetaAnalytic/AnalyticAudit.lean)

The clean Lean 4.27.0-rc1 rebuild and axiom audit checked 1,783 theorem declarations among 2,074 declarations in 67 analytic modules. The receipt binds the proof sources, the local core inputs, and the pinned dependencies. [Kernel audit and source hashes](../../adapters/MockThetaAnalytic/verification.json)

## Replay

The replay reconstructs the bilateral coefficients from \(4,268\) canonical residues and compares them to the signed lattice. With \(c=s-x\) and \(\lambda=am^2\), the substitution \(v=\sqrt{c+it}\) gives the finite-mode integral
\[
\int_0^\infty \frac{i e^{-\lambda t}}{\sqrt{c+it}}\,dt
= \frac{\sqrt{\pi}}{\sqrt{-i\lambda}}\,
  e^{-i\lambda c}\operatorname{erfc}\!\left(\sqrt{-i\lambda}\sqrt{c+i0}\right).
\]
The infinite reference uses independent Poisson-summed quadrature. At \(x=-1/34\), another reference comes from the two terminating cusp sums. The two references agree to \(10^{-27}\) in the replay. The finite prefix through degree \(4267\) has absolute period error \(1.2811\), with a proved allowance of \(62.1083\) rounded up. The test also covers both sides of \(x=s\), sector additivity, and the effect of dropping the normalization factor. Quadrature is checked by precision and order replication. [Replay and exact phase controls](../../adapters/MockThetaAnalytic/check_shadow_period.py) · [Receipt](../../evidence/current/quantum-radial/shadow-period.json)

Run from the repository root with the pinned Lean/Lake toolchain and `mpmath==1.3.0`.

    python3 adapters/MockThetaAnalytic/check_shadow_period.py | diff -u evidence/current/quantum-radial/shadow-period.json -
    (cd adapters/MockThetaAnalytic && python3 verify_analytic.py)

At \(D=4267\), the last square-index mode is \(320\) and the translated endpoint bound is \(24\). Comparing the lane-based estimate with the independent terminating order‑34 sum gives an absolute error of approximately \(0.3698197810\) for each of \(X=0,30030,-1\). The first two sources share their primary remainder and order‑10 phase. Their mod‑17 readings are \(0\) and \(8\), giving different order‑34 phases and different complex endpoints. The replay checks the larger degree cutoffs for \(n=1,2,10,1000\) with exact integer arithmetic. [Translated comparisons and cutoff checks](../../evidence/current/quantum-radial/shadow-period.json)
