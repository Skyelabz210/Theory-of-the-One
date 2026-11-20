# Exact residue packets for Ramanujan's third-order mock theta function

## Result and scope

This formalization connects a named Ramanujan series to compatible coefficient
packets and exact finite root evaluation. It constructs the coefficients of

$$
f(q)=\sum_{n\geq0}\frac{q^{n^2}}{\prod_{j=1}^{n}(1+q^j)^2}
     =\sum_{d\geq0}a_dq^d
$$

by a terminating formal division recurrence, proves that the required reciprocal
is unique, and proves that each coefficient depends on only finitely many
summands. Those coefficients instantiate generic packet reconstruction,
refinement, and finite evaluation theorems. A separate algebraic observation
layer supplies compatible residue families, cylinder functions, and the exact
arithmetic target requirement already supported by the coupled-anchor theory.
The final `mockTheta_from_coupled_anchors` declaration composes that existing
observation contract with the actual named coefficient transform.
The declarations are in [MockTheta.lean](../../formal/universal/MockTheta.lean),
[ResidueSeries.lean](../../formal/universal/ResidueSeries.lean), and
[ProfiniteObservations.lean](../../formal/universal/ProfiniteObservations.lean).

The starting research archive was published in commit
[`8941f734f7c4cfcfae006bce35f8f9a2665a9c52`](https://github.com/Skyelabz210/Theory-of-the-One/commit/8941f734f7c4cfcfae006bce35f8f9a2665a9c52).
Its [arbitrary-moduli paper](../../foundations/profinite_bridge/2026-11-20/whitepaper/Arbitrary_Moduli_in_CRAM.md)
and [revised profinite-bridge paper](../../foundations/profinite_bridge/2026-11-20/profinite_bridge/The_Profinite_Bridge_Revised.md)
contain the mathematical context and distinguish ordinary proofs, historical
formal receipts, finite experiments, and open analytic questions. This review
describes the new finite and coefficientwise Lean layer; it does not turn every
statement in those papers into a compiler-checked theorem.

### Historical family order is not root order

Ramanujan's original seventeen examples are grouped as four third-order, ten
fifth-order, and three seventh-order examples in the
[January 12, 1920 letter](https://www.imsc.res.in/~rao/ramanujan/newnow/lastletter.pdf).
These are historical family labels. They do not assert that roots used in
evaluation have multiplicative orders only three, five, or seven. The
[Folsom–Ono–Rhoades paper](https://afolsom.people.amherst.edu/FolsomOnoRhoades-ForumPi.pdf)
defines the displayed third-order function and gives its radial result at
primitive roots of every even order; this analytic theorem remains an external
literature result here.

The new named-series construction covers **this one function, $f$**. It does
not define or formalize all seventeen functions. The generic coefficient packet
theorems are reusable for additional functions once their actual coefficient
constructions and defining identities are supplied. The count seventeen and the
family labels are source metadata, not a Lean classification theorem.

## Source-to-proof map

| Source | Main objects and declarations | Established scope |
|---|---|---|
| [ResidueSeries.lean](../../formal/universal/ResidueSeries.lean) | `packet`, `weightedPacket`, reconstruction, refinement, periodic evaluation, and finite root evaluation | Generic coefficientwise and finite algebra over bundled semiring/ring structures |
| [MockTheta.lean](../../formal/universal/MockTheta.lean) | `divideBinomial`, `inverseSquaredPochhammer`, `mockCoeff`, named cylinders, and `mockTheta_from_coupled_anchors` | A specific formal coefficient construction for the displayed $f$, connected to packets, compatible observations, and the finite transform |
| [ProfiniteObservations.lean](../../formal/universal/ProfiniteObservations.lean) | `PeriodFamily`, `ResiduePoint`, cylinder refinement, `reducedTargetPeriod`, and target recoverability | Algebraic compatible-coordinate data and exact finite observation requirements |
| [CoupledAnchors.lean](../../formal/universal/CoupledAnchors.lean) | `resolution`, `source_period`, `target_period_iff`, and `combined_target_iff` | Existing LCM/GCD kernel and target-admission theorems for positive, possibly overlapping anchors |
| [ExactObservation.lean](../../formal/universal/ExactObservation.lean) | `FiberConstant`, `Observed`, and `recoverable_iff` | A query factors through observed data exactly when it is constant on observation fibers |
| [MockThetaSmoke.lean](../../formal/universal/MockThetaSmoke.lean) | Independent coefficient-array oracle and exercised packet/evaluation APIs | Executed finite integer regression evidence, recorded separately from universal proofs |

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
theorems instantiate the generic constructions with the actual `mockCoeff`.

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

This composition is itself present in Lean as
`mockTheta_from_reduced_winding`, with positive $M,H,b$, the reduced
divisibility premise, and the root certificate stated explicitly.
`mockTheta_from_coupled_anchors` then takes the existing
`ExactObservation.FiberConstant (anchorObservation ...) (affineTarget ...)`
contract for a positive anchor list. It obtains the reduced divisibility from
`combined_target_fiber_constant_iff`, proves positivity of the coupled
resolution, and invokes the named finite transform at
$P=M\,\operatorname{resolution}(M,\text{anchors})$. Thus the connection to
the existing observation criterion is a declaration with a proof, rather than
only a suggested composition of APIs.

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

In particular, $z^b=1$ never implies that $z$ has exact order $b$, and
neither finite root theorem requires primitivity. This layer does not turn the
universal residue requirement into a claim about the exact order of an
arbitrary ring element or about a mock theta function's analytic singularities.

## 5. Verification and independent finite evidence

The fresh proof audit is recorded in
[`verification.json`](../../evidence/current/profinite-mock-theta/verification.json),
which lists proof-source hashes, theorem declarations, and transitive axiom
dependencies. The companion
[`execution.json`](../../evidence/current/profinite-mock-theta/execution.json)
records commands, compiler/Lake identity, source hashes including the runner and
configuration, log hashes, and the final smoke assertion count. Counts from an
earlier research archive are not evidence that these new files were compiled.

The 20 November 2026 run passed with Lean **4.27.0-rc1**, using its bundled
standard library and no Mathlib dependency. The proof audit compiled in a fresh
temporary build and did not reuse project `.olean` files. It checked **202
theorem declarations**, of which **72** are in this new slice:

| New module | Audited theorem declarations |
|---|---:|
| `ResidueSeries` | 29 |
| `ProfiniteObservations` | 21 |
| `MockTheta` | 22 |

The audit found no admitted proofs or custom axioms. Its transitive axiom lists
contain only `Classical.choice`, `Quot.sound`, and `propext`; **40 of the 202
declarations** have empty axiom lists. The proof audit, Lake build, original
closure smoke program, and new mock-theta smoke program all returned exit zero
without compiler warnings or errors. The recorded source hashes match the
reviewed files.

[MockThetaSmoke.lean](../../formal/universal/MockThetaSmoke.lean) implements an
independent finite coefficient oracle. It uses the explicit factor coefficients
$(-1)^k(k+1)$ at degree $jk$ for $(1+q^j)^{-2}$, performs finite array
convolution, and applies the $n^2$ shifts. This oracle does not call the
formal division recurrence or the named coefficient constructor it checks.

The smoke program exercises coefficient values, degree-preserving packets,
overlapping composite refinement, finite weighted packets, zero truncation,
modulus one, signed coefficients, and a root-premise negative control. Its root
cases instantiate the ring with `Int` and use the integer roots $+1$ and
$-1$ when their period premise holds. Weights outside the complex unit disc
are deliberate because these are finite polynomial identities. Those checks
make no inference about complex radial limits, analytic convergence, or mock
modularity. The universal Lean declarations and the finite smoke executions
are complementary evidence with separately recorded scope.

The [new smoke log](../../evidence/current/profinite-mock-theta/mock-theta-smoke.log)
reports **6,251 exact assertions**: 41 independent coefficients, 1,717
coefficient packets, 1,258 coefficient refinements, 1,625 oracle weighted
packets, 888 weighted refinements, 360 root cases with two oracle assertions
each, and two sign/premise controls. The
[original closure smoke log](../../evidence/current/profinite-mock-theta/closure-smoke.log)
also passed its 1,809 comparison/divmod/GCD pairs and four refusal/negative
controls. These are executed assertion counts, not additional universal theorem
counts.

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
| Formalization of all seventeen original examples | Separate named coefficient definitions and theorems connecting each to the reusable packet layer |
| Production CRAM implementation | Authentic observation constructors, permitted runtime operations, admission and rejection behavior, and conformance proofs |

The external analytic statements discussed in the paper remain attributed to
their original sources: [Folsom–Ono–Rhoades](https://afolsom.people.amherst.edu/FolsomOnoRhoades-ForumPi.pdf),
[Griffin–Ono–Rolen](https://math.vanderbilt.edu/rolenl/rama_mock_live.pdf),
[Rhoades](https://pmc.ncbi.nlm.nih.gov/articles/PMC3651474/), and
[Bringmann–Rolen](https://www.mi.uni-koeln.de/Bringmann/mock_definition_publish.pdf).
Local radial subtraction, a harmonic-Maass analytic shadow, and CRAM's
designated shadow-eleven role remain distinct constructions until an explicit
additional theorem connects them.

The contribution of this slice is concrete: the displayed named series now has
an exact coefficient construction with proved reciprocal uniqueness and local
finiteness, reusable packet/refinement laws, and a finite evaluation interface
that can consume the same admitted-period divisibility established by the
observation arithmetic.
