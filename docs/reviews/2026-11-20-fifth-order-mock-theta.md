# Fifth-order mock theta coefficients and residue observations

Ramanujan's last letter lists two groups of five fifth-order functions. The
letter repeats the labels $f,\phi,\psi,\chi,F$ in each group. Subscript
zero identifies the first group in modern notation. The formalization uses
the unilateral definitions in Bin Chen's Theorem 3.2.
[Letter transcription, p. 4](https://www.imsc.res.in/~rao/ramanujan/newnow/lastletter.pdf#page=4)
· [Bin Chen, *Mock theta functions and Appell–Lerch sums*, Thm. 3.2](https://pmc.ncbi.nlm.nih.gov/articles/PMC6061538/)

## The five zero-subscript series

Write $(a;s)_n=\prod_{j=0}^{n-1}(1-a s^j)$, with $(a;s)_0=1$.
Each function is the sum over $n\ge0$ of the indicated summand. The
rightmost column gives the degree of the leading monomial of that summand.

| Series | Summand | Leading degree |
|---|---|---:|
| $f_0$ | $q^{n^2}/(-q;q)_n$ | $n^2$ |
| $\phi_0$ | $q^{n^2}(-q;q^2)_n$ | $n^2$ |
| $\psi_0$ | $q^{(n+1)(n+2)/2}(-q;q)_n$ | $(n+1)(n+2)/2$ |
| $\chi_0$ | $q^n/(q^{n+1};q)_n$ | $n$ |
| $F_0$ | $q^{2n^2}/(q;q^2)_n$ | $2n^2$ |

The products in $\phi_0$ and $\psi_0$ multiply the numerator. The factors
in $\chi_0$ are $1-q^j$ for $n+1\le j\le 2n$. Its leading degree grows
linearly. A square cutoff valid for $f_0$ would omit genuine contributions
to $\chi_0$. For all five functions only finitely many summands can affect
degree $d$, since every listed leading degree is at least $n$.

Two printed terms clarify the choice of normalization. The IMSc
transcription shows $q/(1+q^2)$ as the first nonconstant $f_0$ summand.
Chen's definition gives $q/(1+q)$, consistent with the subsequent product
in the letter. Its coefficient of $q^2$ in $f_0$ is $-1$. For $\chi_0$ the letter's first nonconstant summand is
$q/(1-q^2)$, matching Chen's $q^n$ numerator. Folsom's paper prints
$q^{n^2+n}$ on p. 4143, which yields zero at degree one. The present
definition gives coefficient one there.
[Letter transcription, p. 4](https://www.imsc.res.in/~rao/ramanujan/newnow/lastletter.pdf#page=4)
· [Chen, Thm. 3.2](https://pmc.ncbi.nlm.nih.gov/articles/PMC6061538/)
· [A. Folsom, *A Short Proof of the Mock Theta Conjectures*, p. 4143](https://afolsom.people.amherst.edu/Folsom-PAMS-Mock-Final.pdf#page=1)

The letter records the cross-function identity
$\chi_0(q)+\phi_0(-q)=2F_0(q)$. Folsom cites this identity to Watson on
p. 4144. For degree $d$, its two sides are compared as
$[q^d]\chi_0+(-1)^d[q^d]\phi_0=2[q^d]F_0$.
[Letter transcription, p. 4](https://www.imsc.res.in/~rao/ramanujan/newnow/lastletter.pdf#page=4)
· [Folsom, p. 4144](https://afolsom.people.amherst.edu/Folsom-PAMS-Mock-Final.pdf#page=2)

The next line of the letter supplies another comparison involving $f_0$ and
$\psi_0$ alongside $F_0$ and $\phi_0$.

$$
f_0(-q)+2F_0(q^2)-2
=\phi_0(-q^2)+\psi_0(-q)
=2\phi_0(-q^2)-f_0(q).
$$

The $\chi_0$ oracle also checks the second expansion printed in the letter,

$$
\chi_0(q)=1+\sum_{n\ge0}\frac{q^{2n+1}}{(q^{n+1};q)_{n+1}}.
$$

In this form the first denominator is $1-q$. In the defining series the
first nonempty denominator is $1-q^2$. Together the two coefficient
calculations exercise both endpoints of the moving factor range.
[Letter transcription, p. 4](https://www.imsc.res.in/~rao/ramanujan/newnow/lastletter.pdf#page=4)

## Lean and execution evidence

The shared finite product acts at consecutive exponents in an arithmetic
progression. `reciprocalProduct_unique` identifies the reciprocal of a
denominator with positive starting exponent. For a nondecreasing leading
degree $e(n)\ge n$, `shiftedCoeff_stable` proves that summing the first
$K$ summands suffices at degree $d<e(K)$. Substitution from the table gives
the square, triangular, linear, and doubled-square cutoffs.
[Shared definitions](../../formal/universal/FifthOrderSeries.lean)

In `MockThetaFifthZero`, `coeff` selects a coefficient sequence through
one of five `Family` cases. `coeff_stable` proves the bound for each case,
and the five aliases `fCoeff`, `phiCoeff`, `psiCoeff`, `chiCoeff`, and
`bigFCoeff` expose the individual sequences. [Zero-subscript module](../../formal/universal/MockThetaFifthZero.lean)

The named coefficient sequences specialize degree packets, weighted packets,
cylinders on compatible residue coordinates, and the finite root transform.
For positive $M,b$, positive anchors, an admitted target query, and $z^b=1$,
the `from_coupled_anchors` theorem evaluates the coefficient truncation at $tz$ using
the complete packet distribution at period $M\,\mathrm{resolution}(M,\mathrm{anchors})$.
The finite sum retains degrees $0\le d<N$.

The fifth-order zero-subscript smoke run passed **2,133 exact assertions**.
An independent integer oracle forms truncated factor arrays, multiplies them,
and applies the numerator shifts. The tests include signed-source cylinders,
weighted packet refinement from period 6 to 3, and a primitive fourth root
in $\mathbb{F}_5$ at the coupled period 12. The same anchors admit a
target of period 4 and reject one of period 5. The cross-function checks compare the
named coefficients through degree 40 in $\mathbb{Z}[q]/(q^{41})$.
The infinite identities above are attributed to their sources.
[Smoke source](../../formal/universal/FifthZeroSmoke.lean)
· [Zero-subscript log](../../evidence/current/profinite-mock-theta/fifth-zero-smoke.log)

The fresh audit compiled 267 theorem declarations. Alongside the four original
third-order series, this checkpoint covers **nine of the seventeen** original
examples. The five one-subscript fifth-order and three seventh-order
coefficient constructions are still open at this revision.
[Proof audit](../../evidence/current/profinite-mock-theta/verification.json)
· [Execution receipt](../../evidence/current/profinite-mock-theta/execution.json)
