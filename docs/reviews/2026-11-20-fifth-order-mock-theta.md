# Fifth-order mock theta coefficients and residue observations

Ramanujan's last letter lists two groups of five fifth-order functions. The
letter repeats the labels $f,\phi,\psi,\chi,F$ in each group. Subscript
zero identifies the first group and subscript one the second. The formalization uses
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

## The five one-subscript series

Chen gives the second group with the following summands, again for $n\ge0$.

| Series | Summand | Leading degree |
|---|---|---:|
| $f_1$ | $q^{n(n+1)}/(-q;q)_n$ | $n(n+1)$ |
| $\phi_1$ | $q^{(n+1)^2}(-q;q^2)_n$ | $(n+1)^2$ |
| $\psi_1$ | $q^{n(n+1)/2}(-q;q)_n$ | $n(n+1)/2$ |
| $\chi_1$ | $q^n/(q^{n+1};q)_{n+1}$ | $n$ |
| $F_1$ | $q^{2n(n+1)}/(q;q^2)_{n+1}$ | $2n(n+1)$ |

The $\chi_1$ denominator runs from $1-q^{n+1}$ through $1-q^{2n+1}$.
The $F_1$ denominator uses the odd exponents from 1 through $2n+1$.
Both have length $n+1$. At $n=0$ each already contains $1-q$, so its
reciprocal contributes one at **every** degree. Lean proves these statements
in `chi_summand_at_index_zero` and `bigF_summand_at_index_zero`. The letter
shows both initial geometric series on page 5. On page 4, the IMSc
transcription repeats $q^6$ in the $n=3$ term of $f_1$. Chen's exponent
$n(n+1)$ gives $q^{12}$ there.
[Letter, p. 4](https://www.imsc.res.in/~rao/ramanujan/newnow/lastletter.pdf#page=4)
· [Letter, p. 5](https://www.imsc.res.in/~rao/ramanujan/newnow/lastletter.pdf#page=5)
· [Chen, Thm. 3.2](https://pmc.ncbi.nlm.nih.gov/articles/PMC6061538/)
· [One-subscript module](../../formal/universal/MockThetaFifthOne.lean)

Folsom records Watson's identity
$\chi_1(q)=2F_1(q)+q^{-1}\phi_1(-q)$.
The smoke test multiplies by $q$ and compares ordinary polynomial
coefficients in $q\chi_1(q)=2qF_1(q)+\phi_1(-q)$ through degree 41.
This reaches coefficient 40 of both $\chi_1$ and $F_1$. At that endpoint,
$140=2\cdot 71-2$, using the independently checked coefficient
$[q^{41}]\phi_1(q)=2$. Thus the shifted comparison holds modulo $q^{42}$.
[Folsom, p. 4144](https://afolsom.people.amherst.edu/Folsom-PAMS-Mock-Final.pdf#page=2)
· [One-subscript test](../../formal/universal/FifthOneSmoke.lean)

## Lean and execution evidence

The shared finite product acts at consecutive exponents in an arithmetic
progression. `reciprocalProduct_unique` identifies the reciprocal of a
denominator with positive starting exponent. For a nondecreasing leading
degree $e(n)\ge n$, `shiftedCoeff_stable` proves that summing the first
$K$ summands suffices at degree $d<e(K)$. Substitution from the table gives
the square, triangular, linear, and doubled-square cutoffs.
[Shared definitions](../../formal/universal/FifthOrderSeries.lean)

In `MockThetaFifthZero` and `MockThetaFifthOne`, `coeff` selects a coefficient sequence through
one of five `Family` cases. `coeff_stable` proves the bound for each case,
and the five aliases `fCoeff`, `phiCoeff`, `psiCoeff`, `chiCoeff`, and
`bigFCoeff` expose the individual sequences in each namespace. [Zero-subscript module](../../formal/universal/MockThetaFifthZero.lean)
· [One-subscript module](../../formal/universal/MockThetaFifthOne.lean)

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
target of period 4 and reject one of period 5. The zero-subscript cross-function checks compare the
named coefficients through degree 40 in $\mathbb{Z}[q]/(q^{41})$.
The infinite identities above are attributed to their sources.
[Smoke source](../../formal/universal/FifthZeroSmoke.lean)
· [Zero-subscript log](https://github.com/Skyelabz210/Theory-of-the-One/blob/63cd3a7723ed4a986322b6ad0f83c668dbc4c05b/evidence/current/profinite-mock-theta/fifth-zero-smoke.log)

The one-subscript suite passed **2,135 exact assertions**. In addition to
402 checks per series, it confirms the two index-zero geometric summands at
degrees 0 through 40, checks $[q^{41}]\phi_1$ independently, and compares
all 42 coefficients of the shifted Watson identity. The full proof audit
compiled 282 theorem declarations. [One-subscript log](https://github.com/Skyelabz210/Theory-of-the-One/blob/63cd3a7723ed4a986322b6ad0f83c668dbc4c05b/evidence/current/profinite-mock-theta/fifth-one-smoke.log)
· [Proof audit](https://github.com/Skyelabz210/Theory-of-the-One/blob/63cd3a7723ed4a986322b6ad0f83c668dbc4c05b/evidence/current/profinite-mock-theta/verification.json)

The zero-subscript checkpoint at `a028a79` compiled 267 theorem declarations.
Its 28,912 mock theta assertions cover the original third-order group and the
five zero-subscript functions. [Zero-subscript checkpoint](https://github.com/Skyelabz210/Theory-of-the-One/blob/a028a794b0eccdac35281b09dae825455d0ea73e/evidence/current/profinite-mock-theta/execution.json)

Together the two groups account for all ten original fifth-order functions.
At the fifth-order checkpoint, fourteen of the seventeen original functions had
coefficient constructions and finite transform theorems. The later
[seventh-order review](2026-11-20-seventh-order-mock-theta.md) covers the
remaining three series. Infinite analytic evaluations, radial limits, and
analytic shadows remain open. [Proof audit](https://github.com/Skyelabz210/Theory-of-the-One/blob/63cd3a7723ed4a986322b6ad0f83c668dbc4c05b/evidence/current/profinite-mock-theta/verification.json)
· [Fifth-order checkpoint execution](https://github.com/Skyelabz210/Theory-of-the-One/blob/63cd3a7723ed4a986322b6ad0f83c668dbc4c05b/evidence/current/profinite-mock-theta/execution.json)
