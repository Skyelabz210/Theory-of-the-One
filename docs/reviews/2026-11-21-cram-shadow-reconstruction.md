# Recovering the analytic shadow from S6 coefficient readings

Let \(f(x)=\sum_{d\ge0}a_dx^d\) be Ramanujan’s third-order function. Degree-labeled S6 observations \((d,a_d\bmod30030)\) for \(0\le d\le D\) recover its six prime-11 shadow sectors through Fourier degree \(24D+1\). The reconstruction inverts the observed parity series, lifts the resulting bits to signed eta coefficients and applies a first moment. The finite series converge to the differential shadow at positive height. The Hecke square uses the recovered eta sectors as its weight-\(1/2\) input. [Observation and reciprocal](../../adapters/MockThetaAnalytic/ShadowReadings.lean) · [Analytic reconstruction](../../adapters/MockThetaAnalytic/ShadowReconstruction.lean)

## The observation contract

A prefix retains every coefficient’s public degree, including degree zero. The decoder uses the parity of each canonical S6 residue, which agrees with parity for every signed representative because \(30030=2\cdot3\cdot5\cdot7\cdot11\cdot13\). The formal series reciprocal over \(\mathbb F_2\) satisfies
\[
 b_0=1,\qquad b_d=\sum_{i=1}^d a_i b_{d-i}\pmod2 .
\]
The input must have constant coefficient one. A real acquisition must bind the observations to the same series, operation and epoch. The recurrence only uses degrees at most \(d\). Refining the prefix preserves already recovered terms. The decoder computes the sector from the public Fourier exponent. The same-source mod-121 anchor control gives identical outputs when projected to the same primary observations. [S6 parity factorization and prefix theorem](../../adapters/MockThetaAnalytic/ShadowReadings.lean)

Removing the even factor leaves coefficients \(0\) and \(15015\) indistinguishable at degree 1. Their reciprocal bits differ there, producing 0 and \(-20\) at \(q^{25}\). To test aggregation on unit prefixes, use two degree-31 inputs with reciprocal supports \(\{0,1,2,15,26\}\) and \(\{0,1,5,7,15,22\}\). Their input parity totals agree in each degree class mod 11, while their \(q^{49}\) coefficients after recovery are 28 and 0. The exact checker also tests signed lifts, missing and duplicate degree labels, noncanonical residues and incompatible unit or square support. [Observation controls](../../evidence/current/analytic-shadow/reconstruction.json)

## From \(f\bmod2\) to the shadow

The double denominator factor \((1+x^j)^2\) becomes \(1+x^{2j}\) in characteristic two. In the product for distinct odd parts, shifting every selected part up by two gives a factor \(x^{2n}\) on the row with \(n\) selections. Selecting the first odd part gives the term \(x^{2n-1}\) times the row with \(n-1\) selections. The same recurrence holds for \(x^{n^2}/\prod_{j=1}^n(1+x^{2j})\). Comparing coefficients below the product cutoff proves
\[
 f(x)\equiv\prod_{j\ge1}(1+x^{2j-1})\pmod2 .
\]
The even factors are the square of \(P(x)=\prod_{j\ge1}(1+x^j)\) in this ring. Splitting the product into even and odd factors and cancelling its unit constant term gives \(f^{-1}=P\) coefficientwise. [Marked odd product and Euler reciprocal](../../adapters/MockThetaAnalytic/ShadowParity.lean)

In the Euler product, distinct partitions with the same weight pair under Franklin’s involution. Its moves exchange the smallest row and the initial consecutive diagonal. They preserve weight and undo each other. The empty partition and the consecutive \(k\)-row partitions with smallest part \(k\) or \(k+1\) remain. The latter have degrees \(k(3k-1)/2\) and \(k(3k+1)/2\). Thus \(b_d=1\) exactly when \(24d+1=m^2\). The positive root determines a unique exceptional partition. [Franklin’s involution](../../adapters/MockThetaAnalytic/FranklinRows.lean) · [Cancellation and reciprocal support](../../adapters/MockThetaAnalytic/ShadowPentagonal.lean)

With \(q=e^{2\pi iz}\), the signed lift recovers \(\eta(24z)=q\prod_{j\ge1}(1-q^{24j})\). Each moved pair changes the number of parts by one and therefore cancels in the signed product as well. The exceptional \(k\)-row sign is \((-1)^k\). In terms of the positive square root \(m\), this is \(\chi_{12}(m)\), taking values \(+1,-1,-1,+1\) at \(1,5,7,11\bmod12\). The first moment multiplies the coefficient by \(4m\chi_4(m)\). The product \(\chi_4\chi_{12}\) gives the signed unary theta character of the normalized shadow. The sector label is \(r=-m^2\bmod11\) because \(\xi_{1/2}\) conjugates the translation projector. The existing completion proof identifies the limiting sector as \(\xi_{1/2}(P_rM_f)\). [Differential identity and sector sign](../../adapters/MockThetaAnalytic/MockCompletion.lean)

For \(|q|\le \rho<1\), put \(s=\lfloor\sqrt{24D+1}\rfloor+1\). Each sector error is at most \(4\sum_{m\ge s}m\rho^{m^2}\). A numerical bound follows from \((s+j)^2\ge s^2+2sj\).
\[
4\rho^{s^2}\left(\frac{s}{1-\rho^{2s}}+
        \frac{\rho^{2s}}{(1-\rho^{2s})^2}\right).
\]
At height at least \(y_0>0\), use \(\rho=e^{-2\pi y_0}\). The exact replay uses the nomes \(1/2,-1/2,i/2,19/20\), seven cutoffs and an independent larger signed-lattice sum with its own tail allowance. [Uniform error theorem](../../adapters/MockThetaAnalytic/ShadowReconstruction.lean) · [Exact replay](../../adapters/MockThetaAnalytic/check_shadow_reconstruction.py)

## The Hecke square at five

On the five nonzero occupied classes, expand the eta masks in the even characters \(\xi\bmod11\). The resulting unary theta characters are \(\chi_{12}\xi\). The trivial imprimitive component is obtained by removing the terms with \(11\mid m\). Those terms form the zero sector, a unary series dilated by 121. The weight-\(1/2\) unary theta theorem puts these forms at level dividing \(4\cdot132^2=69696\). For the odd theta target the nebentypus factor \((\frac{-4}{\cdot})\) cancels the extra \(\chi_4\) on units. The square dilation contributes a trivial character on units. The two sets of forms therefore have compatible characters at a common \(\Gamma_1\) level of 69696. Five is a good prime. [Serre–Stark, weight \(1/2\)](https://doi.org/10.1007/BFb0065296) · [Purkait, weight \(3/2\), §2](https://arxiv.org/pdf/1205.7086)

For one scalar character \(\epsilon\) and Fourier degree \(n\), the independent arithmetic coefficient rules are
\[
\begin{aligned}
 [q^n]\,5T_{1/2}(25)b
   &=5b(25n)+\epsilon(5)\Big(\frac{n}{5}\Big)b(n)+\epsilon(5)^2 b(n/25),\\
 [q^n]\,T_{3/2}(25)a
   &=a(25n)+\epsilon(5)\Big(\frac{-n}{5}\Big)a(n)+5\epsilon(5)^2 a(n/25).
\end{aligned}
\]
Nonintegral indices contribute zero. At \(n=m^2\) the Legendre symbols agree. The first moment \(J\) satisfies \(4(5m)\chi_4(5m)=5(4m\chi_4(m))\). This gives the coefficient identity
\[
J\big(5T_{1/2}(25)b\big)=T_{3/2}(25)(Jb)
\]
for square-index packets \(b\) with the given diamond actions. In sector coordinates diamond multiplication supplies \(\chi_{12}(5)=-1\) and shifts the sector by multiplication by \(5^2\). The resulting action on either column sends the series with label \(r\) to the series with label \(4r\bmod11\) with factor \(-6\). The ordinary crank matrix \(C\) for sizes 2 through 7 has determinant 1 and a verified integer inverse. Writing \((Rv)_r=v_{4r\bmod11}\), the action on the joint crank readings is \(C(-6R)C^{-1}\). [Hecke stencils and crank counts](../../adapters/MockThetaAnalytic/ShadowHecke.lean) · [Coefficient convention](https://doi.org/10.5802/jtnb.865)

For output through Fourier degree 4096, mock degree 4267 supplies the required lookahead through Fourier degree 102400. The exact replay checks 24,582 sector comparisons and 24,582 joint crank comparisons, including transport by \(C(-6R)C^{-1}\). The full transformed \(q^1\) coefficient is \(-24\). Zero-padding the missing \(q^{25}\) input gives \(-4\). Using the fixed size-three mask on the output degree gives zero at \(q^1\). Transporting the joint crank readings gives \(-24\) in the size-three component. [Lookahead and fixed mask controls](../../evidence/current/analytic-shadow/reconstruction.json)

## Reproduction and evidence

Run from the repository root with Python 3.11 or newer and the pinned Lean/Lake toolchain.

    python3 adapters/MockThetaAnalytic/check_shadow_reconstruction.py | diff -u evidence/current/analytic-shadow/reconstruction.json -
    python3 tools/verify_profinite_mock_theta.py --lean lean
    (cd adapters/MockThetaAnalytic && python3 verify_analytic.py)

Lean verifies the finite algebra, coefficient identity, analytic limit, and Hecke stencil equality. The identification of the stencils with the geometric Hecke operators uses the cited modular-form theorems. The executable check concerns the research observation contract and the specified analytic series. [Recorded kernel audit](../../adapters/MockThetaAnalytic/verification.json)

The existing finite suite reproduced 367 audited theorem declarations and 44,196 exact mock theta and crank assertions in a fresh checkout at the source base `6a04e4b`. [Core verification command and source coverage](../../evidence/current/profinite-mock-theta/README.md)
