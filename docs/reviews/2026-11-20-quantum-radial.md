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
The odd-order cusp is regular for the displayed $f$ series. The order-11
singular example below specializes a different rank character.
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

This proof uses the interior absolute tail at each chosen radius. A fixed
truncation has a finite polynomial value at $\zeta$ while $b(t\zeta)$ can
diverge. The finite sum defining $B_k$ uses summand index $n<k$, a
different cutoff from the coefficient degree $d<N_j$.

The standard-library Lean construction freezes the factor
$(-\zeta;\zeta)_n^2$ at the supplied root and applies the finite character
transform to the remaining exponent $n+1$. Once $\zeta^k=-1$ and $k>0$,
the tail vanishes identically. An admitted target of order $2k$ supplies
$2k\mid L$ at the coupled-anchor period. The identity identifying this
finite expression as the radial limit is FOR's theorem.
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
odd denominator. That statement concerns $G,H$. Quantum modularity of
the repository's own boundary packet observables would require specifying
their slash action and proving regularity of its defect.
[Zagier, Example 1, equations (8), (10), (11)](https://people.mpim-bonn.mpg.de/zagier/files/qmf/fulltext.pdf#page=5)
· [FOR, pp. 8–9, Theorem 1.3 and its vector-valued interpretation](https://afolsom.people.amherst.edu/FolsomOnoRhoades-ForumPi.pdf#page=8)

## Evidence by layer

| Object | What establishes the result |
|---|---|
| All 17 mock theta coefficient families | Lean coefficient, packet, refinement and finite root theorems |
| Mod-11 crank of a partition | Lean proves S6 projection, S8 recovery under an authentic affine transition, and the independent seventh-order size-weighted finite crank pairing |
| Third-order $f$ and its normalized shadow | Exact Lean coefficients and mod-11 support. Zwegers supplies modularity. The worked analytic derivation and pointwise numerics specify the factor 4 and the opposite residue under $\xi_{1/2}$ |
| FOR's even-order boundary sum | Lean finite product and tail termination. FOR Theorem 1.1 identifies the compensated radial limit |
| Approaching the boundary by coefficient packets | The cutoff argument above composes the interior coefficient transform with the published radial limit |
| Rank/crank limit at the eleventh root | FOR Theorem 1.2 with the statistic character and cusp specified separately |
| Modular transformations on rational cusps | Zagier's Example 1 and FOR's Theorem 1.3 include their domains, weights and regularity statements |

The exact suite passed 1,579 checks, including 133 for order-eleven rank/crank
specializations. Independent numerical checks evaluate the corrected
interior functions on four radial paths and repeat at higher precision.
[Exact smoke program](../../formal/universal/QuantumRadialSmoke.lean) · [Radial numerical receipt](../../evidence/current/quantum-radial/numerical.json)

[Coefficient coverage](2026-11-20-seventh-order-mock-theta.md)
· [Third-order shadow](2026-11-20-third-order-analytic-shadow.md)
· [Radial evidence and reproduction](../../evidence/current/quantum-radial/README.md)
