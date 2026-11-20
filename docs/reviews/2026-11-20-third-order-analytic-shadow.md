# The analytic shadow of Ramanujan's third-order f at modulus eleven

Let $e(z)=\exp(2\pi i z)$, $z=x+iy$ with $y>0$, and $q=e(z)$.
Ramanujan's third-order function and its integer-exponent normalization are

$$
f(q)=\sum_{n\ge0}\frac{q^{n^2}}{\prod_{j=1}^n(1+q^j)^2}
     =\sum_{d\ge0}a_dq^d,\qquad
M_f^+(z)=q^{-1}f(q^{24})=\sum_{d\ge0}a_d q^{24d-1}.
$$

In particular the $d=0$ term is $q^{-1}$. The project constructs $a_d$ by
formal division. On each closed disk $|q|\le\rho<1$, expanding the factors
absolutely gives a majorant
$\prod_{j\ge1}(1-\rho^j)^{-2}\sum_{n\ge0}\rho^{n^2}<\infty$.
The product is finite since $-\log(1-\rho^j)\le\rho^j/(1-\rho)$.
Thus the same coefficients give the analytic $f$ in the open unit disk, and
they can be grouped by degree modulo 11 there.
[Coefficient construction](../../formal/universal/MockTheta.lean)
· [Watson, *The Final Problem*, p. 62](https://www.mi.uni-koeln.de/NumberTheory/teaching/Seminare/MockTheta/pages/vortragS06.pdf#page=30)

## Completion and the factor four

Zwegers proves the modular transformation and Casimir eigenvalue for a
three-component weight-$1/2$ completion. Use its first component $H_0=F_0-G_0$
in the normalization of Ono's equations (3.1)–(3.4). With $\tau\in\mathbb H$,

$$
\begin{aligned}
 F_0(\tau)&=e(-\tau/24) f(e(\tau)),\\
 g_1(w)&=-\sum_{n\in\mathbb Z}(n+1/6)e\!\left(\tfrac32(n+1/6)^2w\right)
        =-\tfrac16\!\sum_{m\equiv1\ (6)}m\,e(m^2w/24),\\
 G_0(\tau)&=2i\sqrt3\int_{-\bar\tau}^{i\infty}
        \frac{g_1(w)}{\sqrt{-i(w+\tau)}}\,dw,\qquad M_f(z)=H_0(24z).
\end{aligned}
$$

Here $m$ runs through signed integers in $1+6\mathbb Z$. The square root is
the principal branch and the path may run vertically. The radicand has positive real part throughout the upper half-plane. The Gaussian
decay of $g_1$ gives locally uniform convergence of the integral and its
kernel derivatives away from the real boundary.
[Zwegers, *Mock θ-functions and real analytic modular forms*](https://doi.org/10.1090/conm/291/04907)
· [Ono, §3.1, p. 29, equations (3.1)–(3.4) and Theorem 3.1](https://swc-math.github.io/aws/2013/2013OnoNotes.pdf#page=29)

Use $\xi_k U=2iy^k\overline{\partial_{\bar z}U}$ with
$\partial_{\bar z}=(\partial_x+i\partial_y)/2$. In the integral the
integrand is holomorphic in $\tau$. Differentiating the lower endpoint gives
$\partial_{\bar\tau}G_0=2i\sqrt3\, g_1(-\bar\tau)/\sqrt{2\operatorname{Im}\tau}$.
Since $g_1$ has real coefficients, conjugation gives
$\xi_{1/2}H_0=-2\sqrt6\,g_1$. Dilation by $c>0$ gives
$\xi_k(U(c\,\cdot))(z)=c^{1-k}(\xi_k U)(cz)$. At $c=24$ these factors give

$$
\boxed{\displaystyle
\xi_{1/2}M_f(z)=4\Theta(z),\qquad
\Theta(z)=\sum_{m\equiv1\ (6)} m\,q^{m^2}
         =q-5q^{25}+7q^{49}-11q^{121}+13q^{169}+\cdots.}
$$

This sign uses $H_0=F_0-G_0$. The chain rule accounts for the
$\sqrt{24}$ between the two coordinate systems. $M_f^+$ by itself is
holomorphic and has $\xi_{1/2}M_f^+=0$. The nonholomorphic correction
supplies the displayed shadow.
[Published operator convention, Ono, §3.2, p. 31](https://swc-math.github.io/aws/2013/2013OnoNotes.pdf#page=31)

An explicit Fourier expansion makes the nonholomorphic term computable.
Writing $w=-\bar\tau+it$ in $G_0$ reduces each integral to
$\int_0^\infty e^{-at}(2\operatorname{Im}\tau+t)^{-1/2}\,dt$ with
$a=\pi m^2/12$. Substituting $u=a(2\operatorname{Im}\tau+t)$ gives the
upper incomplete gamma function $\Gamma(1/2,v)=\int_v^\infty u^{-1/2}e^{-u}\,du$.
At $\tau=24z$ this yields

$$
 M_f(z)=q^{-1}f(q^{24})
   -\frac{2}{\sqrt\pi}\!\sum_{m\equiv1\ (6)}
        \operatorname{sgn}(m)\,\Gamma(1/2,4\pi m^2y)\,q^{-m^2}.
$$

The bound $\Gamma(1/2,v)\le v^{-1/2}e^{-v}$ cancels the growth of
$q^{-m^2}$ and leaves Gaussian decay on each $y\ge\eta>0$.
It justifies termwise integration and locally uniform summation.
Using $\partial_v\Gamma(1/2,v)=-v^{-1/2}e^{-v}$ in each Fourier term
also gives $4m q^{m^2}$ under $\xi_{1/2}$.

## Projecting the completion by degree modulo 11

Write $\zeta=e(1/11)$. For a differentiable one-periodic function $U$ on the
upper half-plane define its projection onto Fourier exponents $r\bmod 11$ by

$$
 (P_rU)(z)=\frac1{11}\sum_{j=0}^{10}\zeta^{-rj}U(z+j/11).
$$

For a term $b_n(y)e(nx)$, translation by $j/11$ multiplies it by
$\zeta^{nj}$. Summing the geometric progression keeps precisely
$n\equiv r\pmod{11}$. The translation fixes $y$ and commutes with
$\partial_{\bar z}$. Conjugating the scalar in $\xi_{1/2}$ reverses $r$,
so $\xi_{1/2}P_r U=P_{-r}\xi_{1/2} U$. The scaled $M_f$ has period one
by the translation law for $H_0$. Applying the identity to its completion gives

$$
 \boxed{\displaystyle
 \xi_{1/2}(P_rM_f)(z)
   =4\!\sum_{\substack{m\equiv1\ (6)\\m^2\equiv-r\ (11)}} m\,q^{m^2}.}
$$

The theta series converges absolutely and locally uniformly for $y>0$ by the
Gaussian bound $\sum_{m\in\mathbb Z}|m|e^{-2\pi y m^2}<\infty$.
The holomorphic part retains original degrees $d$ satisfying $24d-1\equiv r$,
equivalently $d\equiv6(r+1)\pmod{11}$. These formulas describe a projection
of the entire completed function and its restriction to the named coefficients.

The squares modulo 11 are $0,1,3,4,5,9$. Thus the projected completions with
$r=1,3,4,5,9$ have zero shadow. Each remaining projected shadow has a nonzero
coefficient. For a given square exponent the two signed square roots have
opposite residues modulo 6, so at most one lies in $1+6\mathbb Z$.

| Completion class $r$ | Shadow degree class $-r$ | Example signed $m$ | Coefficient of $q^{m^2}$ in $\xi_{1/2}(P_rM_f)$ |
|---:|---:|---:|---:|
| 0 | 0 | $-11$ | $-44$ |
| 2 | 9 | $19$ | $76$ |
| 6 | 5 | $7$ | $28$ |
| 7 | 4 | $13$ | $52$ |
| 8 | 3 | $-5$ | $-20$ |
| 10 | 1 | $1$ | $4$ |

## What a shadow-eleven observation supplies

The exponent $24d-1$ indexes a Fourier degree. The earlier crank theorem counts
partitions by their signed crank at a fixed size and obtains the class from an
authentic S8 transition $Y=X+881790s$, with $s$ the crank. If that transition
instead carries a signed Fourier degree, the arithmetic returns the corresponding
degree class. Computing a projected analytic function also requires its
coefficients, normalization, nonholomorphic correction and summation over the
retained degrees. For example $m=1$ and $m=67$ give the same signed residue
and the same square residue modulo 11, with different coefficients and exponents
in $4\Theta$. The completed-function identity above specifies exactly which
degree observation commutes with the analytic operator. A construction of that
completion from partition crank observations remains open.
[Shadow-eleven observation contract](../../formal/universal/CrankShadow11.lean)
· [Partition crank character construction](2026-11-20-crank-shadow-eleven.md)
· [Earlier formulation of the analytic question, §8](../../foundations/profinite_bridge/2026-11-20/profinite_bridge/The_Profinite_Bridge_Revised.md#8-the-analytic-obstruction-and-the-remaining-conjecture)

## Verification by result

Zwegers supplies the modular transformation theorem for the completed vector.
The differential and projection arguments above are written mathematical proofs.
The standard-library Lean module proves the coefficient support of the Laurent
series and its finite evaluation at any ring unit. For a positive square root
$m$, `shadowWeight` is $m$ at $m\equiv1\pmod6$, $-m$ at $m\equiv5\pmod6$,
and zero otherwise. The signed-lattice theorem identifies these coefficients
with $\Theta=-6g_1(24z)$. On their nonzero support, $d\equiv1\pmod{24}$, and
$d\equiv0\pmod{11}$ holds exactly when the coefficient is divisible by 11.
The theorem `shadowCoeff_sector_support_iff` proves that the six degree
sectors $0,1,3,4,5,9$ are exactly the ones with a nonzero integer
coefficient. The square at $d=121$ has coefficient $-11$ in $\Theta$ and
$-44$ in $4\Theta$.
[Exact coefficient theorems](../../formal/universal/MockThetaShadow.lean)

The finite suite passed 9,504 exact assertions. It checks the Laurent
normalization against signed rank parity through original degree 40, then
tests coefficients of $\Theta$ against the bilateral lattice through square
degree 625. The residue tests inspect both a degree and its signed amplitude.
At $m=-5$, the degree 25 is in class 3 modulo 11 while its coefficient in
$\Theta$ is $-5$. The suite includes character evaluations in the field of 23
elements and a control for the pole and dilation in the field of 101 elements.
[Exact checks](../../formal/universal/MockThetaShadowSmoke.lean)
· [Fresh proof audit](../../evidence/current/profinite-mock-theta/verification.json)
· [Exact execution log](../../evidence/current/profinite-mock-theta/third-order-shadow-smoke.log)

At $z=1/7+i/40$, $-2/11+i/16$, and $2/9+i/8$, a 65-decimal-digit
calculation compares the vertical Eichler integral with the complementary
error function expansion. The largest absolute difference was below
$2.10\times10^{-45}$. A two-dimensional finite difference of the full
completion, at refined step $5\times10^{-19}$, agreed with $4\Theta$ to
within $1.73\times10^{-33}$. At the first point, all eleven projected
derivatives agreed with the predicted opposite-degree projections within
$4.30\times10^{-33}$. Keeping $+r$ in place of $-r$ at classes 1 and 10
produced differences greater than 3.4. The receipt records the truncation
bounds and the step-halving comparison. Quadrature, roundoff, and
differentiation errors were assessed numerically.
[Checker](../../tools/check_analytic_shadow.py)
· [Pointwise numerical receipt](../../evidence/current/analytic-shadow/numerical.json)
