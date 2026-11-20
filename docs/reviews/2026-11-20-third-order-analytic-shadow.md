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

Guerzhoy, Kent, and Ono also display the same scaled $M_f$ and its integral.
Their theta function in the integrand is $-6g_1(w)$, whose first power is
$e(w/24)$. Below, $\Theta(z)=-6g_1(24z)$ has integer exponents. The
differential operator fixes the scalar relating that series to $\xi_{1/2}M_f$.
[Guerzhoy–Kent–Ono, p. 6169](https://doi.org/10.1073/pnas.1001355107)
· [Author manuscript, p. 1](https://uva.theopenscholar.com/files/ken-ono/files/125.pdf#page=1)

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
In fact, for $y\ge\eta>0$ the absolute value of the $m$th correction
term is at most $e^{-2\pi m^2\eta}/(\pi|m|\sqrt\eta)$. Its first $x$ and
$y$ derivatives are each bounded by $6|m|e^{-2\pi m^2\eta}/\sqrt\eta$,
using $\partial_v\Gamma(1/2,v)=-v^{-1/2}e^{-v}$. Both majorants are summable.
Thus differentiating the entire correction term by term is valid on the upper
half-plane. Each signed Fourier term gives $4m q^{m^2}$ under $\xi_{1/2}$.

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
The Mathlib package below checks the differential and projection operations independently.
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

## Complex analysis in Lean

The analytic adapter compiles 83 explicitly declared theorems across 12
modules, 58 public and 25 private. The kernel audited 195 constants,
including 164 theorem entries with generated helpers, and recorded their
transitive axiom dependencies. The adapter imports the exact `shadowWeight` from
the standard-library package. At every $|u|<1$ it proves absolute summability of
$\sum_{m\ge0}\operatorname{shadowWeight}(m)u^{m^2}$, using $m|u|^m$ as a
summable majorant. It proves that the eleven degree bins sum to the entire
series, and that normalized translation by elevenths selects the bin with the
prescribed exponent. This applies both to signed Laurent monomials and to
the convergent theta series in the upper half-plane.
[Convergence](../../adapters/MockThetaAnalytic/ShadowConvergence.lean)
· [Fourier degree projections](../../adapters/MockThetaAnalytic/ShadowProjection.lean)

Lean defines $\xi_{1/2}$ from the real Fréchet derivative. It proves that
$\xi_{1/2}P_r=P_{-r}\xi_{1/2}$ when the function is real differentiable
at all eleven translates. The generic theorem `xiHalf_project11_of_shadow`
takes the shadow identity at those points as input. For the named Fourier
completion, `xiHalf_project11_mockCompletion` discharges that input at all
eleven translates using the differentiated infinite series.
[Operator and index reversal](../../adapters/MockThetaAnalytic/ShadowOperator.lean)
· [Hypotheses of the completed projection](../../adapters/MockThetaAnalytic/ShadowProjection.lean)

For the nonholomorphic Fourier modes, Lean differentiates the complementary
error function defined by a Gaussian integral. The theorem
`xiHalf_finiteCompletion` combines this calculation with the actual mock
coefficients. For every holomorphic cutoff $D$ and magnitude cutoff $M$, it
differentiates that finite completion and obtains four times the signed unary
sum through $m=M$. At each $y>0$,
`tendsto_xiHalf_finiteCompletion` proves those derivatives converge to
$4\Theta(z)$ as $M\to\infty$ for any choice $D=D(M)$. The theorem takes
the limit after differentiation. At the earlier checkpoint this was the
strongest differential result verified for the named $f$.
[Fourier modes, finite completion, and limiting theorem](../../adapters/MockThetaAnalytic/ShadowMode.lean)
· [Finite-completion audit at `4b90453`](https://github.com/Skyelabz210/Theory-of-the-One/blob/4b90453cb7fe510f9afb790a2d57ca2b8b52e6e2/adapters/MockThetaAnalytic/verification.json)
· [Reproduction](../../adapters/MockThetaAnalytic/README.md)

### Differentiating the completed function

The new `mockCompletion` is the sum of the defining hypergeometric
$Q^{-1}f(Q^{24})$ and the infinite signed error-function series above, where
$Q=e(z)$. Lean proves the holomorphic part complex differentiable on the
upper half-plane. For $|q|\le r<1$, it bounds the $n$th defining summand of
$f$ by $(r^n/(1-r)^2)^n$, which is eventually bounded by $2^{-n}$.
Thus the $\xi_{1/2}$-derivative of the holomorphic part vanishes.
[Holomorphicity of the defining series](../../adapters/MockThetaAnalytic/MockHolomorphic.lean)

On every region $y\ge a>0$, the correction terms and their first real
derivatives admit a common summable majorant. Lean derives the Gaussian
tail bound for $\operatorname{erfc}$ and uses a quadratic polynomial in $m$
times $e^{-2\pi a m}$ as majorant. At height $y>0$, it can therefore
differentiate the whole correction term by term on a neighborhood with
height above $y/2$. The theorem `hasFDerivAt_nonholomorphicPart` identifies
the real Fréchet derivative of the sum with the sum of the mode derivatives.
[Gaussian tail](../../adapters/MockThetaAnalytic/ShadowGaussian.lean)
· [Uniform mode bounds](../../adapters/MockThetaAnalytic/ShadowBounds.lean)
· [Infinite derivative](../../adapters/MockThetaAnalytic/ShadowInfinite.lean)

Consequently `xiHalf_mockCompletion` proves $\xi_{1/2}M_f=4\Theta$
at every $y>0$ for the explicitly defined Fourier completion.
`xiHalf_project11_mockCompletion_eq_zero_iff` proves its projected
shadow vanishes identically exactly for $r=1,3,4,5,9$. Each of the other
six projections has a nonzero value somewhere in the upper half-plane.
The proof isolates the first nonzero term in its bin and lets $Q$ tend to
zero on the positive real axis.
[Completion and projected shadows](../../adapters/MockThetaAnalytic/MockCompletion.lean)
· [Nonvanishing proof](../../adapters/MockThetaAnalytic/ShadowSectors.lean)

The equality with the Eichler-integral convention is derived above from
the published formula. Zwegers supplies the completed vector's modular
transformation law and Casimir eigenvalue. A differential identity alone
allows a holomorphic summand such as $z$, which changes the translation
law while preserving $\xi_{1/2}$. The compensated boundary limit at a
root of unity is a separate input from Folsom–Ono–Rhoades.
[Radial theorem and its hypotheses](2026-11-20-quantum-radial.md)
· [Current analytic proof audit](../../adapters/MockThetaAnalytic/verification.json)
