# Exact residue packets for Ramanujan's third-order mock theta functions $f$ and $\phi$

## Result and scope

Lean constructs the coefficients of Ramanujan's third-order functions $f$ and $\phi$.

$$
f(q)=\sum_{n\ge0}\frac{q^{n^2}}{\prod_{j=1}^{n}(1+q^j)^2},
\qquad
\phi(q)=\sum_{n\ge0}\frac{q^{n^2}}{\prod_{j=1}^{n}(1+q^{2j})}.
$$

In each case a terminating formal division recurrence gives the unique
denominator reciprocal. The numerator shift makes each coefficient a finite
sum. Both coefficient functions instantiate packet refinement, cylinder
observation, and finite evaluation at the period supplied by the coupled-anchor
theorem. Ramanujan wrote the first terms of $\phi$ on page 3 of his last letter.
Watson gives the product formula and the relation to $f$ used in §5.
[Ramanujan's letter, p. 3](https://www.imsc.res.in/~rao/ramanujan/newnow/lastletter.pdf#page=3)
· [Watson, pp. 62–63](https://www.mi.uni-koeln.de/NumberTheory/teaching/Seminare/MockTheta/pages/vortragS06.pdf#page=30)

The starting research archive was published in commit
[`8941f734f7c4cfcfae006bce35f8f9a2665a9c52`](https://github.com/Skyelabz210/Theory-of-the-One/commit/8941f734f7c4cfcfae006bce35f8f9a2665a9c52).
Its [arbitrary-moduli paper](../../foundations/profinite_bridge/2026-11-20/whitepaper/Arbitrary_Moduli_in_CRAM.md)
and [revised profinite-bridge paper](../../foundations/profinite_bridge/2026-11-20/profinite_bridge/The_Profinite_Bridge_Revised.md)
contain the mathematical context and distinguish ordinary proofs, historical
formal receipts, finite experiments, and open analytic questions. This review
describes the new finite and coefficientwise Lean layer; it does not turn every
statement in those papers into a compiler-checked theorem.

### Historical family labels and root orders

Ramanujan's original seventeen examples are grouped as four third-order, ten
fifth-order, and three seventh-order examples in the
[January 12, 1920 letter](https://www.imsc.res.in/~rao/ramanujan/newnow/lastletter.pdf).
These labels describe the series. The certificate $z^b=1$ in the finite
evaluation theorem determines the allowed roots. Folsom, Ono, and Rhoades
prove a separate analytic result for $f$ at primitive roots of every even
order. [Folsom–Ono–Rhoades](https://afolsom.people.amherst.edu/FolsomOnoRhoades-ForumPi.pdf)

The current Lean package covers **two of the seventeen named examples**, $f$ and $\phi$.
The other two third-order, ten fifth-order, and three seventh-order functions
each need a coefficient construction.

## Source-to-proof map

| Source | Main objects and declarations | Established scope |
|---|---|---|
| [ResidueSeries.lean](../../formal/universal/ResidueSeries.lean) | `packet`, `weightedPacket`, reconstruction, refinement, periodic evaluation, and finite root evaluation | Generic coefficientwise and finite algebra over bundled semiring/ring structures |
| [MockTheta.lean](../../formal/universal/MockTheta.lean) | `divideBinomial`, `inverseSquaredPochhammer`, `mockCoeff`, named cylinders, and `mockTheta_from_coupled_anchors` | A specific formal coefficient construction for the displayed $f$, connected to packets, compatible observations, and the finite transform |
| [MockThetaPhi.lean](../../formal/universal/MockThetaPhi.lean) | `inverseEvenPochhammer`, `phiCoeff`, `phiCylinder`, and `phi_from_coupled_anchors` | Unique reciprocal of the even-stride product, coefficient support, and the finite transform for $\phi$ |
| [CoefficientObservations.lean](../../formal/universal/CoefficientObservations.lean) | `coefficientCylinder` and `finite_root_evaluation_from_coupled_anchors` | Cylinder observations and the coupled-anchor transform for a supplied coefficient function |
| [ProfiniteObservations.lean](../../formal/universal/ProfiniteObservations.lean) | `PeriodFamily`, `ResiduePoint`, cylinder refinement, `reducedTargetPeriod`, and target recoverability | Algebraic compatible-coordinate data and exact finite observation requirements |
| [CoupledAnchors.lean](../../formal/universal/CoupledAnchors.lean) | `resolution`, `source_period`, `target_period_iff`, and `combined_target_iff` | Existing LCM/GCD kernel and target-admission theorems for positive, possibly overlapping anchors |
| [ExactObservation.lean](../../formal/universal/ExactObservation.lean) | `FiberConstant`, `Observed`, and `recoverable_iff` | A query factors through observed data exactly when it is constant on observation fibers |
| [MockThetaSmoke.lean](../../formal/universal/MockThetaSmoke.lean) | Independent integer coefficient calculations, packet and evaluation checks, and the joint Watson check | Finite regression evidence over the integers and the field of five elements |

## 1. Constructing the named coefficients

### Triangular formal division

`MockTheta.Series R` is the coefficient function type `Nat → R`. The construction
uses a commutative ring through Lean's bundled algebra hierarchy. It does not
assume a field or use division by a potentially noninvertible coefficient.

For a positive integer $j$, the coefficient action of multiplication by
$1+u q^j$ is

$$
(B_{j,u}a)_d=
\begin{cases}
a_d+u a_{d-j},&j\leq d,\\
a_d,&d<j.
\end{cases}
$$

`divideBinomial` solves $B_{j,u}b=a$ by

$$
b_d=
\begin{cases}
a_d-u b_{d-j},&j\leq d,\\
a_d,&d<j.
\end{cases}
$$

The recursive degree decreases because $j>0$. The code supplies that
termination proof. `mulBinomial_divideBinomial` proves one inverse identity;
`mulBinomial_injective` proves uniqueness coefficient by coefficient; and
`divideBinomial_mulBinomial` proves the other inverse identity. Formal division
here is an explicit operation with a proved inverse law.

### Unique reciprocal denominator

Starting from the constant coefficient series `oneSeries`,
`inverseSquaredPochhammer n` applies division twice for each factor
$1+q^j$, for $1\leq j\leq n$. `denominatorAction n` is the corresponding
composition of binomial multiplication actions. The key declarations are:

- `denominatorAction_inverse`: the constructed reciprocal is sent to the
  constant series one.
- `denominatorAction_injective`: the denominator action is injective.
- `inverseSquaredPochhammer_unique`: any coefficient series sent to one is the
  constructed reciprocal.

This identifies the reciprocal of the specified finite product through its
coefficient action. A full general-purpose formal power-series ring, a field of
analytic functions, and a convergence theorem are not prerequisites of this
construction.

### Local finiteness of the hypergeometric sum

`mockSummand n d` shifts that reciprocal by $n^2$.
`mockSummand_support` proves that the coefficient is zero when $d<n^2$.
The weaker bound $d<n$ is then sufficient for the implementation's finite
coefficient definition:

$$
a_d=\sum_{0\leq n<d+1}[q^d]
       \frac{q^{n^2}}{\prod_{j=1}^{n}(1+q^j)^2}.
$$

`mockCoeff_stable` proves that extending this summand cutoff to any $N>d$
does not change the coefficient. Consequently the infinite written sum has a
well-defined formal coefficient at every degree, without taking an analytic
limit.

The later `mockPolynomial N q` is

$$
f_N(q)=\sum_{0\leq d<N}a_dq^d.
$$

Here $N$ counts retained **coefficient degrees**. It is not the number of
hypergeometric summands used in an analytic truncation. The distinction matters
when comparing a finite computation with the original written series.

### The even-stride denominator of $\phi$

For $\phi$, `inverseEvenPochhammer n` starts at one and divides once by
$1+q^{2j}$ for each $1\le j\le n$. Applying `phiDenominatorAction n` to the
result gives one, and this action is injective. The reciprocal is therefore
uniquely determined over the same commutative ring as $f$.

Write $b_d=[q^d]\phi(q)$. The summand at index $n$ vanishes at degree $d<n^2$,
and `phiCoeff_stable` proves that summing over $0\le n<K$ gives $b_d$
whenever $d<K^2$. At $d=k^2$ the $k$th summand contributes the constant
term of its reciprocal, which is one. The transform uses the coefficient truncation $\phi_N(q)=\sum_{d<N}b_dq^d$.
[Coefficient construction](../../formal/universal/MockThetaPhi.lean)

## 2. Coefficient packets and finite pushforward

For any coefficient function $a$, `packet a M r d` retains both the degree
and the residue test:

$$
P_{M,r}(a)_d=
\begin{cases}
a_d,&d\equiv r\pmod M,\\
0,&\text{otherwise}.
\end{cases}
$$

For $M>0$, `packet_reconstruction` recovers $a_d$ by summing over the
canonical residue indices $0\leq r<M$. `packet_refinement` proves the
coefficientwise pushforward law for $m\mid M$:

$$
P_{m,r}(a)_d=
\sum_{\substack{0\leq s<M\\s\equiv r\pmod m}}P_{M,s}(a)_d.
$$

This construction does not collapse infinitely many coefficients into a scalar
residue bucket. The degree remains available in `packet`.

`weightedPacket` performs the separate, finite summation. With weights
$w_d=t^d$, write

$$
C_{N,M,r}(t)=
\sum_{\substack{0\leq d<N\\d\equiv r\pmod M}}a_dt^d.
$$

`weightedPacket_mass` proves conservation of the finite weighted sum, while
`weightedPacket_refinement` proves

$$
C_{N,m,r}(t)=
\sum_{\substack{0\leq s<M\\s\equiv r\pmod m}}C_{N,M,s}(t).
$$

Most of this generic packet layer requires only a semiring. The commutative-ring
assumptions used for the named series and the root identity are explicit in
their sections. `mockPacket`, `mockWeightedPacket`, and their refinement
theorems instantiate the generic constructions with `mockCoeff`. The corresponding
$\phi$ instances use `phiCoeff`, `phiPacket`, and `phiWeightedPacket`.

## 3. Compatible residue families and cylinder functions

`ProfiniteObservations.PeriodFamily` declares admitted natural moduli and proves
each admitted modulus positive. `ResiduePoint F` then consists of:

- a natural residue at every admitted modulus;
- a proof that each residue is below its modulus;
- the transition equation $x_n\bmod m=x_m$ whenever the admitted periods
  satisfy $m\mid n$.

These are the algebraic compatible-coordinate data used by an inverse system.
The type does not add a topology, compactness, a topological universal property,
or a directedness/cofinality theorem for an arbitrary `PeriodFamily`.

For an arbitrary admission predicate, the displayed divisibility transitions
also need not impose every common-source CRT constraint between incomparable
moduli. If the family admitted only 6 and 10, for example, those transitions
alone would not require their coordinates to agree modulo 2. A connecting
coordinate, such as their admitted GCD or LCM, supplies that additional
relation. `positivePeriods` includes such connecting periods, and the periods
in `selectedPrimaryPowers` are connected within the power family. The generic
structure should therefore be read with its actual admission assumptions; its
name alone does not establish full common-source compatibility for every
arbitrary choice of periods.

`natPoint` and `intPoint` map a semantic source integer to its compatible
coordinates. The signed construction uses nonnegative Euclidean residues.
Neither construction reconstructs an integer from an arbitrary compatible
tuple, and the code does not assert that every tuple is the image of an
ordinary integer. `ResiduePoint` itself has no scalar source or winding field.

For an admitted period $m$, `ofResidueFunction m g` evaluates the cylinder
function $x\mapsto g(x_m)$. `cylinder_refinement` proves

$$
g(x_m)=g(x_n\bmod m)\qquad(m\mid n).
$$

`cylinder_fiber_constant` and `refined_cylinder_fiber_constant` connect this
identity to the existing observation-fiber criterion. `restrictPoint` forgets
admitted coordinates while preserving the retained compatibility equations;
`restriction_cylinder` records preservation of each retained cylinder value.
None of these declarations manufactures an authentic new observation from
insufficient data.

`MockTheta.lean` instantiates these cylinder functions with the named
coefficients:

$$
\operatorname{mockCylinder}_{m,d}(x)=P_{m,x_m}(a)_d,
\qquad
\operatorname{mockWeightedCylinder}_{t,N,m}(x)=C_{N,m,x_m}(t).
$$

`mockCylinder_on_diagonal` proves the value at a diagonal natural source, and
`mockCylinder_observable` proves that the degree cylinder is constant on fibers
of its finite coordinate. `mockCylinder_refinement` and
`mockWeightedCylinder_refinement` combine tuple coherence with packet
pushforward. In these latter theorems the coarse cylinder value is a **sum of
the appropriate finer packet masses**. It is not identified with a single
finer residue packet. Cylinder functions pull back along a residue reduction;
coefficient masses push forward by summing over that reduction's fibers.

`coefficientCylinder` evaluates the degree packet of any supplied coefficient
function at the selected coordinate. Both `mockCylinder` and `phiCylinder`
use it. Its refinement law sums the finer packets over the selected residue
class, and its observation law gives equal values for points that agree at
the selected coordinate. [CoefficientObservations.lean](../../formal/universal/CoefficientObservations.lean)

The designated primary is fixed explicitly by `selectedPrimary = 30030` and
`selected_primary_factorization`, with `selectedPrimaryPowers` supplying its
power-period family. This preserves S6 $\{2,3,5,7,11,13\}$.
`positivePeriods` is an additional mathematical example of an admission
predicate, not a production constructor for all positive-modulus observations.
The generic parameters in the other theorems do not authorize replacing the
selected primary.

## 4. Exact target admission and finite root evaluation

### Necessary and sufficient arithmetic condition

Fix a primary coefficient $M$, a reference residue $r$, and a positive
target modulus $b$. For the semantic affine source
$X=r+Mk$, define

$$
h_b=\frac{b}{\gcd(M,b)},\qquad
\operatorname{observe}_H(k)=k\bmod H,\qquad
\operatorname{target}_b(k)=(r+Mk)\bmod b.
$$

`target_constant_on_quotient_fibers_iff` proves exactly

$$
\bigl(\forall k,j\in\mathbb Z,\;
k\equiv j\pmod H\Rightarrow
(r+Mk)\equiv(r+Mj)\pmod b\bigr)
\quad\Longleftrightarrow\quad h_b\mid H.
$$

It uses `CoupledAnchors.target_period_iff` and the reduced-kernel identity.
`target_recoverable_iff` expresses the same condition as existence of an answer
function on the image of the observation. As in
[`ExactObservation.recoverable_iff`](../../formal/universal/ExactObservation.lean),
that existence statement is a specification, using the general observation
framework; it does not provide an efficient executable decoder or an authentic
observation producer.

For a list of positive anchors with $L=\operatorname{lcm}(a_1,\ldots,a_s)$,
the existing resolution is

$$
H=\frac{L}{\gcd(M,L)},\qquad MH=\operatorname{lcm}(M,L).
$$

`anchor_observation_eq_iff`, `combined_target_fiber_constant_iff`, and
`combined_target_recoverable_iff` connect the actual list of affine anchor
readings to this same reduced target requirement. Repeated anchors, composites,
and shared factors are handled by the LCM/GCD calculation. Independent product
capacity is not assumed for those dependent readings.

### Sufficient connection to the named finite evaluation

In the finite-period use, take $M,H>0$. The proved interface
`target_divides_source_period` supplies

$$
h_b\mid H\quad\Longrightarrow\quad b\mid MH.
$$

For a commutative ring element $z$ with a certificate $z^b=1$, this implies
$z^{MH}=1$. The generic `finite_root_evaluation_of_dvd` and the named
`mockTheta_finite_root_evaluation_of_dvd` therefore apply at retained packet
period $P=MH$:

$$
\sum_{0\leq r<P}C_{N,P,r}(t)z^r=f_N(tz).
$$

At $P=M\,\operatorname{resolution}(M,\text{anchors})$, the generic theorem
`finite_root_evaluation_from_coupled_anchors` takes the
`ExactObservation.FiberConstant (anchorObservation ...) (affineTarget ...)`
premise for positive anchors and the root certificate $z^b=1$. The premise
supplies $h_b\mid H$ through `combined_target_fiber_constant_iff`.
The named specializations `mockTheta_from_coupled_anchors` and
`phi_from_coupled_anchors` yield $f_N(tz)$ and $\phi_N(tz)$ from their
respective packet distributions.

The packet coefficients must actually be supplied with their stated source and
weight semantics. A divisibility proof alone does not construct those packets.
The equation is a finite ring identity: $t$ has no analytic unit-disc
restriction in its Lean statement.

The complete coefficient-packet distribution
$\{C_{N,P,s}(t):0\leq s<P\}$ is also a different object from the residue
readings of one runtime source $r+Mk$. The left side of the transform uses that
whole packet distribution. The coupled-anchor hypothesis supplies the exact
admission condition for its period; it does not turn one source reading into
all those coefficient masses. The final theorem proves the algebraic identity
under the stated admission contract, not a packet-observation constructor or a
runtime implementation of that constructor.

The arithmetic equivalence and this evaluation implication have different
quantifiers. **$h_b\mid H$ is necessary and sufficient for the universal
target-$b$ residue query above. It is a sufficient admission condition for
the displayed finite evaluation, not a necessary condition for every particular
$f_N,t,z$.** A polynomial may be constant or zero, terms may cancel, $N=0$
may give an empty sum, or the supplied root may have smaller order.

For positive $b$, the certificate $z^b=1$ implies that the multiplicative
order of $z$ divides $b$. Primitivity is an additional condition in general.
Both named finite root evaluations accept any certified root.

## 5. Verification and independent finite evidence

The proof audit compiles every registered project module in a fresh temporary
directory using Lean 4.27.0-rc1 and the bundled standard library. The execution
receipt identifies the compiler, source bytes, commands, and output logs. The
proof audit passed 217 declarations, with empty axiom lists for 41. The
remaining declarations use only `propext`, `Classical.choice`, and `Quot.sound`. [Execution receipt](../../evidence/current/profinite-mock-theta/execution.json)
· [Proof receipt](../../evidence/current/profinite-mock-theta/verification.json)

The mock theta smoke run passed **12,803 exact assertions**. The independent
coefficient checks cover $d=0,\ldots,40$ for each series.
The $f$ oracle expands each $(1+q^j)^{-2}$ with coefficient $(-1)^k(k+1)$ at
degree $jk$. The $\phi$ oracle expands each $(1+q^{2j})^{-1}$ with
coefficient $(-1)^k$ at degree $2jk$. The initial coefficients of $\phi$ are
$1,1,0,-1,1,1,-1,-1,0,2,0,-2$. The cases $d=8$ and $d=9$ straddle the
first contribution of $n=3$, and have values $0$ and $2$. Both series are
also exercised through their finite packet and root evaluation interfaces.
For $\phi$ the smoke program checks the selected coordinate on signed integer
points and evaluates at the primitive fourth root $z=2$ in $\mathbb{F}_5$.
Using $t=4$ gives $tz=3$ in that field. With
$M=3$ and anchors 4 and 6, the resolution is 4 and the retained period is 12.
[Smoke source](../../formal/universal/MockThetaSmoke.lean)
· [Execution log](../../evidence/current/profinite-mock-theta/mock-theta-smoke.log)

Watson relates the two series by

$$
\bigl(2\phi(-q)-f(q)\bigr)\prod_{j\ge1}(1+q^j)
=1+2\sum_{k\ge1}(-1)^k q^{k^2}.
$$

At degrees $0$ through $40$, only the factors $1+q^j$ with $j\le40$ can
contribute. The smoke program forms the product from the named Lean
coefficients and compares each result to the right side. Degree $0$ has
coefficient $1$, a positive square $k^2$ has coefficient $2(-1)^k$, and all
other degrees have coefficient $0$. This run establishes agreement modulo
$q^{41}$. Watson gives the infinite identity in the cited paper.
[Watson, pp. 62–63](https://www.mi.uni-koeln.de/NumberTheory/teaching/Seminare/MockTheta/pages/vortragS06.pdf#page=30)

The original $f$ implementation passed 202 theorem declarations, including 72
in the initial coefficient and observation modules, and 6,251 mock theta
assertions. It has a separate immutable execution record.
[Original $f$ receipts at `853ed93`](https://github.com/Skyelabz210/Theory-of-the-One/tree/853ed937d0fa3545683d668e72f6439b599529b5/evidence/current/profinite-mock-theta)

From the repository root, reproduce the recorded audit/build/smoke sequence with
Python 3.11 or newer and the pinned Lean/Lake installation available together:

```sh
python3 tools/verify_profinite_mock_theta.py --lean lean
```

The [runner](../../tools/verify_profinite_mock_theta.py) writes fresh current
receipts, checks that the formal source hashes remain unchanged throughout the
run, and replaces previous success records if an attempt fails. It requires no
external Python package or network access once the pinned toolchain is
installed.

## 6. Architectural and analytic boundaries

The current [machine contract](../ARCHITECTURE.md) remains in force. A machine
must retain authentic residue/anchor evidence and establish configuration,
source, operation, phase, and epoch bindings. Compatible numbers or a positive
admission predicate do not independently authenticate those conditions.
Additional observations preserve the selected primary; their resolution is
counted through the actual compatible periods. The semantic integers $X$ and
$k$ appearing in proofs are not prescriptions to store scalar winding or to
insert scalar reconstruction into the residue compute path.

This slice does not claim any of the following:

| Further result | What remains beyond the present declarations |
|---|---|
| Topological profinite completion or Pontryagin duality | Topological objects, continuity, compactness, dual-group construction, and the corresponding theorems |
| Cofinality of the fully refined affine star family | A formal statement and proof of the additional admission/refinement hypotheses from the paper |
| Infinite analytic Fourier/measure identity | Convergence, summability, complex evaluation, and the justified limiting operation |
| Radial mock theta asymptotics | Root-dependent subtraction and analytic control at the unit circle |
| Analytic shadow correspondence | Explicit analytic and observation-side operators with an intertwining theorem |
| Formalization of all seventeen original examples | Coefficient definitions for the remaining fifteen functions and their specializations of the packet theorems |
| Production CRAM implementation | Authentic observation constructors, permitted runtime operations, admission and rejection behavior, and conformance proofs |

The external analytic statements discussed in the paper remain attributed to
their original sources: [Folsom–Ono–Rhoades](https://afolsom.people.amherst.edu/FolsomOnoRhoades-ForumPi.pdf),
[Griffin–Ono–Rolen](https://math.vanderbilt.edu/rolenl/rama_mock_live.pdf),
[Rhoades](https://pmc.ncbi.nlm.nih.gov/articles/PMC3651474/), and
[Bringmann–Rolen](https://www.mi.uni-koeln.de/Bringmann/mock_definition_publish.pdf).
Local radial subtraction, a harmonic-Maass analytic shadow, and CRAM's
designated shadow-eleven role remain distinct constructions until an explicit
additional theorem connects them.
