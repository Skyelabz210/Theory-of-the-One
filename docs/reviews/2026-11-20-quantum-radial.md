# From the finite packets of f to quantum radial values

Folsom, Ono, and Rhoades (FOR) compute the finite value left after subtracting
the singular part of Ramanujan's third-order $f$ at an even-order root of
unity. In the repository this gives a specific target for the coefficient
packets of $f$ and a finite polynomial that can be evaluated exactly at the
root. Write $e(x)=\exp(2\pi i x)$ and $(a;q)_n=\prod_{j=0}^{n-1}(1-aq^j)$,
with $(a;q)_0=1$.

## The even-order cusp

Let $\zeta$ be a primitive root of **exact** order $2k$, $k\ge1$. Write

$$
 f(q)=\sum_{n\ge0}\frac{q^{n^2}}{(-q;q)_n^2},\qquad
 b(q)=\frac{(q;q)_\infty}{(-q;q)_\infty^2},\qquad
 B_k(\zeta)=-4\sum_{n=0}^{k-1}\zeta^{n+1}(-\zeta;\zeta)_n^2 .
$$

FOR's Theorem 1.1 states

$$
 \lim_{t\uparrow1}\left[f(t\zeta)-(-1)^k b(t\zeta)\right]=B_k(\zeta),
 \qquad 0<t<1 .
$$

The two analytic functions are evaluated at the same interior point
before subtraction. The right side terminates because
$(-\zeta;\zeta)_n=\prod_{j=1}^n(1+\zeta^j)$ contains $1+\zeta^k=0$
as soon as $n\ge k$. At $\zeta=-1$ the single retained term gives 4 and
the compensating expression is $f+b$. At $\zeta=i$ the two terms inside
the sum are $i$ and $-2i$, so $B_2(i)=4i$ and the expression is $f-b$.
FOR notes that the defining series for $f$ converges at odd-order roots.
The order-11 singular example below specializes a different rank character.
[FOR, pp. 3–5, Theorem 1.1 and examples](https://afolsom.people.amherst.edu/FolsomOnoRhoades-ForumPi.pdf#page=4)

## Two limits and the CRAM observation

Write $f_N(q)=\sum_{d<N}a_dq^d$. The Lean transform computes this polynomial
from its complete coefficient packets at a period $L$ with $2k\mid L$.
For each fixed $0<t<1$, absolute convergence gives
$f_N(t\zeta)\to f(t\zeta)$ as $N\to\infty$. The radial parameter $t$ belongs
to the open disk throughout that limit. The published boundary value follows
by taking the compensated radial limit afterwards.
[Coefficients and coupled-anchor proof](../../formal/universal/MockTheta.lean)
· [Absolute convergence of f in the disk](2026-11-20-third-order-analytic-shadow.md)

A single sequence also suffices. Given any $t_j\in(0,1)$ tending to 1, for each
$j\ge1$ choose a cutoff $K_j\ge j$ with
$\sum_{d\ge K_j}|a_d|t_j^d<1/j$. The cutoffs may be chosen increasing.
Then for **every** sequence $N_j\ge K_j$,

$$
 \left|f_{N_j}(t_j\zeta)-(-1)^kb(t_j\zeta)-B_k(\zeta)\right|
 \le \frac1j+
 \left|f(t_j\zeta)-(-1)^kb(t_j\zeta)-B_k(\zeta)\right|\longrightarrow0 .
$$

The Mathlib theorem `for_limit_from_f_packets` implements this transfer with
the named coefficient function, the hypergeometric series `radialF`, and
the modular product `radialB`. Its hypotheses include the Taylor identity
inside the disk, FOR's compensated radial limit, a primitive $2k$th root,
and a positive period $L$ with $2k\mid L$. The auxiliary theorem
`exists_packet_cutoffs` obtains an error at most $1/(j+1)$ from pointwise
convergence of each interior Taylor series. Every larger cutoff works.
The theorem `hasSum_radialF_coefficients` now proves that Taylor identity throughout the disk. For general even order, `for_limit_from_f_packets_of_radial_law` takes FOR’s radial limit as its analytic input. At order 34, Lean proves that input for every primitive root and composes it with the packet theorem at $e^{2\pi i/34}$. [Order-34 radial proof](../../adapters/MockThetaAnalytic/FOROrder34.lean) [Initial cutoff transfer](../../adapters/MockThetaAnalytic/QuantumRadialLimit.lean) · [Taylor identification and strengthened transfer](../../adapters/MockThetaAnalytic/ThirdOrderTaylor.lean)

This proof uses the interior absolute tail at each chosen radius. A fixed
truncation has a finite polynomial value at $\zeta$ while $b(t\zeta)$ can
diverge. The packet schedule approximates $f$ and uses the modular product
$b(t_j\zeta)$ at that same point. The finite sum defining $B_k$ uses
summand index $n<k$, a different cutoff from the coefficient degree $d<N_j$.

There is also a sufficient cutoff depending only on the radius. Put
$s=1-t$ and $R=1-s/2$. Absolute expansion of the summands of $f$ gives

$$
 \sum_{d\ge0}|a_d|R^d
 \le \prod_{j\ge1}(1-R^j)^{-2}\sum_{n\ge0}R^{n^2}
 \le \frac{2}{s}e^{8/s^2}.
$$

Indeed $-\log(1-R^j)\le R^j/(1-R)$, so the log of the product is at most
$2R/(1-R)^2\le8/s^2$. The last sum is bounded by the geometric series
$1/(1-R)=2/s$. For every $|\zeta|=1$, the tail after retaining $N$
coefficient degrees satisfies

$$
 \left|f(t\zeta)-f_N(t\zeta)\right|
 \le (t/R)^N\sum_{d\ge0}|a_d|R^d
 \le \frac{2}{s}\exp(8/s^2-Ns/2),
$$

since $t/R=1-s/(2R)\le e^{-s/2}$. Therefore
$N(t)=\lceil18/(1-t)^3\rceil$ gives error at most
$(2/s)e^{-1/s^2}\to0$, uniformly in the chosen root. Combining this bound
with FOR identifies the limit of that particular packet schedule. This bound
on Taylor degrees is conservative. The numerical checker uses the
hypergeometric series with its own truncation estimates.

The standard-library Lean construction freezes the factor
$(-\zeta;\zeta)_n^2$ at the supplied root and applies the finite character
transform to the remaining exponent $n+1$. Once $\zeta^k=-1$ and $k>0$,
the tail vanishes identically. An admitted target of order $2k$ supplies
$2k\mid L$ at the coupled-anchor period. The identity identifying this
finite expression as the radial limit is FOR's theorem. The order-34 case also has a Lean proof from Watson’s disk identity.
[Finite product, termination, and period proofs](../../formal/universal/QuantumRadial.lean)

## The rank and crank at the shadow prime 11

In FOR's notation, $w$ is the character variable for the partition statistic
and $q$ marks the partition size. Their three functions are

$$
\begin{aligned}
 R(w;q)&=\sum_{n\ge0}\frac{q^{n^2}}{(wq;q)_n(w^{-1}q;q)_n},\\
 C(w;q)&=\frac{(q;q)_\infty}{(wq;q)_\infty(w^{-1}q;q)_\infty},\\
 U(w;q)&=\sum_{n\ge0}(wq;q)_n(w^{-1}q;q)_n q^{n+1}.
\end{aligned}
$$

For $1\le a<b$, $1\le h<K$, both fractions $a/b,h/K$ reduced, and $b\mid K$,
put $w=e(a/b)$, $\zeta=e(h/K)$, and choose $hh'\equiv-1\pmod K$.
FOR's Theorem 1.2 gives

$$
 \lim_{t\uparrow1}\!
 \left[R(w;t\zeta)-e(-a^2h'K/b^2)\,C(w;t\zeta)\right]
 =-(1-w)(1-w^{-1})U(w;\zeta).
$$

The phase is independent of the representative $h'$ since $b\mid K$.
For $w=-1$, $R(-1;q)=f(q)$ and $C(-1;q)=b(q)$. At even cusp order
$K=2k$ the phase is $(-1)^k$, recovering Theorem 1.1.

For the prime-eleven example put $w=\zeta=e(1/11)$ and $h'=-1$.
The phase is $\zeta$ and the first factor $1-w^{-1}\zeta=0$ terminates
$U$ after its $n=0$ term. Hence

$$
 \boxed{\displaystyle
 \lim_{t\uparrow1}\left[R(\zeta;t\zeta)-\zeta C(\zeta;t\zeta)\right]
 =(1-\zeta)^2 .}
$$

The Lean `rankCrankRhs_eleventh_root` theorem proves the finite right
side in a commutative ring whenever $w^{11}=1$, using $w^{10}$ as its
inverse. At least one term is retained. The analytic limit is FOR's theorem.
[Two-variable finite sum](../../formal/universal/QuantumRadial.lean)

At order 22, Theorem 1.1 instead applies to $w=-1$ and any primitive
$22$nd root for the size variable. Both 11 and 22 divide the selected CRAM
primary $30030$, so its degree coordinate projects to either modulus.
Evaluation needs the complete distribution of weighted packets at the chosen
period. In the prime-eleven example the two variables happen to use the
same root, with their roles visible in the exponents. In the earlier seventh-order polynomial
$\sum_{n<N}[q^n]\mathcal F_j(q)t^n\sum_r C_r(n)z^r$, each crank histogram
is weighted by a separate mock coefficient. FOR uses the classical product
$C(w;q)$ and the rank generating function with a specified compensating
phase. At size one, `crankEuler_degree_one` proves that the product coefficient
is $w+w^{-1}-1$ for every positive Euler cutoff. The sole ordinary partition
$[1]$ contributes $w^{-1}$. The theorem `crankEuler_minus_ordinary_degree_one`
proves their difference is $w-1$ for an eleventh root with inverse $w^{10}$.
[Size-one Lean proofs](../../formal/universal/QuantumRadial.lean)
[FOR, pp. 5–6, equations (1.4)–(1.6) and Theorem 1.2](https://afolsom.people.amherst.edu/FolsomOnoRhoades-ForumPi.pdf#page=5)
· [Seventh-order finite crank pairing and its partition convention](2026-11-20-crank-shadow-eleven.md)

## What makes a boundary function quantum modular

Zagier specifies a function on rational cusps, a modular group, a weight
and any multiplier. On points where both terms are defined, its defect
$h_\gamma=F-F|_\kappa\gamma$ must extend with prescribed regularity on the
real boundary. In his canonical definition the extension is real analytic
outside finitely many exceptions for each $\gamma$. The defects satisfy
$h_{\gamma_1\gamma_2}=h_{\gamma_1}|_\kappa\gamma_2+h_{\gamma_2}$.
A table of radial constants gives boundary values. Quantum modularity also
requires this transformation and regularity data.
[Zagier, *Quantum Modular Forms*, equations (1)–(3)](https://people.mpim-bonn.mpg.de/zagier/files/qmf/fulltext.pdf#page=2)

### A quantum modular form from the same two-variable series

Set $w=1$ in the repository's $U$ and in FOR equation (1.6). At a root $q$
of exact order $L$ this gives $U(1;q)=\sum_{n=0}^{L-1}(q;q)_n^2 q^{n+1}$.
The first omitted product contains $1-q^L=0$. Bryson, Ono, Pitman, and
Rhoades (BOPR) write this specialization as $U(-1;q)$ because they use
the opposite sign on the statistic variable. Their Theorem 1.1 identifies
it with Kontsevich's strange function
$F(q^{-1})=\sum_{n=0}^{L-1}(q^{-1};q^{-1})_n$ at every root of unity.
For $q=-1$, both expressions give $3$, and for $q=i$ both give $8+3i$.
[BOPR, Theorem 1.1](https://uva.theopenscholar.com/files/ken-ono/files/140_8.pdf#page=2)
· [FOR's convention, p. 7](https://afolsom.people.amherst.edu/FolsomOnoRhoades-ForumPi.pdf#page=7)

BOPR Theorem 1.3 supplies the transformation and regularity for this
particular observable. With the normalization
$\phi(x)=e(-x/24)U(1;e(x))$, the two generator laws are

$$
 \phi(x+1)=e(-1/24)\phi(x),\qquad
 \phi(x)+(-ix)^{-3/2}\phi(-1/x)=h(x).
$$

The inversion formula holds for $x\in(\mathbb Q\cup\mathbb H)\setminus\{0\}$
with the principal power. On the rational boundary the defect is the
eta period integral
$h(x)=\frac{\sqrt3}{2\pi i}\int_0^{i\infty}\eta(u)[-i(x+u)]^{-3/2}\,du$.
It extends smoothly on $\mathbb R$ and is real analytic away from zero.
The interior formula in the source includes a second term. This is the
weight-$3/2$ quantum modular law for $w=1$. The compensated limits above
use $w=-1$ and $w=e(1/11)$, respectively.
[BOPR, Theorem 1.3 and equation (1.5)](https://doi.org/10.1073/pnas.1211964109)
· [Author manuscript, pp. 2–3](https://uva.theopenscholar.com/files/ken-ono/files/140_8.pdf#page=3)

For $\zeta=e(1/11)$, reduction of that finite polynomial modulo
$\Phi_{11}(X)=1+X+\cdots+X^{10}$ gives a degree-nine representative

$$
 U(1;\zeta)=43+22\zeta+22\zeta^2+22\zeta^3+31\zeta^4
  +22\zeta^5+33\zeta^6+19\zeta^7+22\zeta^8+7\zeta^9 .
$$

Lean proves the polynomial identity at every primitive eleventh root.
Its `strangeCusp` takes the actual sum of the $w=1$ terms, proves that it
terminates at a root of unity (including any larger compatible cutoff),
and proves the normalized translation law. The inversion law and regularity
of the eta period are BOPR's analytic result.
[Terminating values and translation in Lean](../../adapters/MockThetaAnalytic/QuantumStrange.lean)

The quantum value is $\phi(1/11)=e(-1/264)U(1;\zeta)$,
approximately $-17.46739925+31.93324223i$. At $x=1/11$, the second
inversion value is $\phi(-11)=e(11/24)$, so the two finite root sums give
a nonzero defect of about $0.77403710+0.33814767i$. Independent integration
of the eta period agrees. At $1/11$, $-11$, and $1/2$ the largest absolute
discrepancy was below $2\times10^{-61}$. The numerical receipt also checks
translation and the independent terminating strange-function sum.
[Numerical transformation checks](../../evidence/current/quantum-radial/numerical.json)

The same root gives $U(\zeta;\zeta)=\zeta$ in FOR's rank/crank limit because its
statistic parameter selects different factors.

### A second example from Zagier

Zagier's Example 1 provides a concrete law. For $x\in\mathbb Q$, $q=e(x)$,
let $Z(x)=e(x/24)\sigma(q)$, where the terminating series at a root is
$\sigma(q)=1+\sum_{n\ge0}(-1)^n q^{n+1}(q;q)_n$. Its weight-one
transformation on $\Gamma_0(2)$ includes

$$
 Z(x+1)=e(1/24)Z(x),\qquad
 \frac{1}{2x+1}Z\!\left(\frac{x}{2x+1}\right)=e(1/24)Z(x)+h(x).
$$

The second equality holds at rational $x\ne-1/2$. The defect extends
smoothly to $\mathbb R$ and is real analytic away from $-1/2$. For instance
$Z(0)=2$ and $Z(1)=2e(1/24)$ follow directly from the terminating formula.
For the distinct Rogers–Fine functions $G,H$, FOR Theorem 1.3(2) gives a
weight-$1/2$ vector transformation under $x\mapsto 1/(2x)$ with an explicit
period integral. In the specialization $(a,b)=(1,2)$ its rational domain
$Q_{1,2}$ consists of positive reduced fractions with odd numerator and
odd denominator. That statement concerns $G,H$. Extending a quantum transformation law to
another specialization of the packet observables would require its own
slash action and a proof of regularity for its defect.
[Zagier, Example 1, equations (8), (10), (11)](https://people.mpim-bonn.mpg.de/zagier/files/qmf/fulltext.pdf#page=5)
· [FOR, pp. 8–9, Theorem 1.3 and its vector-valued interpretation](https://afolsom.people.amherst.edu/FolsomOnoRhoades-ForumPi.pdf#page=8)

## Evidence by layer

| Object | What establishes the result |
|---|---|
| All 17 mock theta coefficient families | Lean coefficient, packet, refinement and finite root theorems |
| Mod-11 crank of a partition | Lean proves S6 projection, S8 recovery under an authentic affine transition, and the independent seventh-order size-weighted finite crank pairing |
| Third-order $f$ and its normalized shadow | Mathlib proves the full Fourier-completion derivative $4\Theta$, the sign reversal of its degree projection, and the exact vanishing sectors. Zwegers supplies the modular transformation law |
| FOR's even-order boundary sum | Lean finite product and tail termination. FOR Theorem 1.1 identifies the compensated radial limit at general even order. Lean proves the limit at every primitive 34th root |
| Approaching the boundary by coefficient packets | Lean proves the Taylor identity in the open disk and the cutoff transfer given a radial limit. The positive-angle order-34 packet theorem discharges that premise |
| Rank/crank limit at the eleventh root | FOR Theorem 1.2 with the statistic character and cusp specified separately |
| $U(1;q)$ at a root | Mathlib proves the terminating sum, the normalized translation law and the prime-11 polynomial. BOPR supplies inversion and analytic regularity, with independent three-cusp numerical checks |
| Other modular transformations on rational cusps | Zagier's Example 1 and FOR's Theorem 1.3 include their domains, weights and regularity statements |

The exact suite passed 1,579 checks, including 133 for order-eleven rank/crank
specializations. Independent numerical checks evaluate the corrected
interior functions on four radial paths and repeat at higher precision.
[Exact smoke program](../../formal/universal/QuantumRadialSmoke.lean) · [Radial numerical receipt](../../evidence/current/quantum-radial/numerical.json)

The order-34 and order-10 values of $B_k$ also enter FKTY’s weight-$1/2$ law on the even-denominator quantum set. At the $-1$ twist of $U$, Lean proves the fixed-pair identity by evaluating the two reflected cusp limits and transporting a primitive of the theta kernel. [Lean period identity](../../adapters/MockThetaAnalytic/EichlerBridge.lean) · [Exact normalization and period](2026-11-20-order-34-to-10.md)

[Coefficient coverage](2026-11-20-seventh-order-mock-theta.md)
· [Third-order shadow](2026-11-20-third-order-analytic-shadow.md)
· [Radial evidence and reproduction](../../evidence/current/quantum-radial/README.md)
