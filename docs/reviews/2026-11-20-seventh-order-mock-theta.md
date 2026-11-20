# The three original seventh-order mock theta functions

Ramanujan's last letter lists three seventh-order series as (i), (ii), and
(iii). In the modern notation $\mathcal F_0,\mathcal F_1,\mathcal F_2$,
their summands are given below. Here
$(a;q)_k=\prod_{j=0}^{k-1}(1-aq^j)$ and $(a;q)_0=1$.
[Letter transcription, p. 5](https://www.imsc.res.in/~rao/ramanujan/newnow/lastletter.pdf#page=5)
· [Bin Chen, eqs. (3.46)–(3.48)](https://pmc.ncbi.nlm.nih.gov/articles/PMC6061538/)
· [Frank Garvan, *New Fifth and Seventh Order Mock Theta Function Identities*, p. 3](https://arxiv.org/pdf/1907.04803#page=3)

| Letter | Series | Index | Summand | Denominator exponents |
|---|---|---|---|---|
| (i) | $\mathcal F_0$ | $n\ge0$ | $q^{n^2}/(q^{n+1};q)_n$ | $n+1,\ldots,2n$ |
| (ii) | $\mathcal F_1$ | $n\ge1$ | $q^{n^2}/(q^n;q)_n$ | $n,\ldots,2n-1$ |
| (iii) | $\mathcal F_2$ | $n\ge0$ | $q^{n(n+1)}/(q^{n+1};q)_{n+1}$ | $n+1,\ldots,2n+1$ |

In (i) the initial summand is the constant series 1. In (ii) it is
$q/(1-q)$. In (iii) it is $1/(1-q)$, so summand zero contributes one in
every coefficient degree. These initial terms give constant coefficients
$1,0,1$ respectively. The calligraphic names distinguish these three
functions from $F_0$ and $F_1$ of fifth order.

## Lean coefficients and finite evaluation

Lean indexes all three summands from $k=0$. For $\mathcal F_1$ the printed
index is $n=k+1$. Its denominator then agrees with that of $\mathcal F_2$
at $k$, while their numerator exponents are $(k+1)^2$ and $k(k+1)$.
The difference is $k+1$. The theorem `f1_summand_eq_f2_shift` proves that
the coefficient at degree $d+k+1$ of the former summand equals the
coefficient at $d$ of the latter for every $k,d$.
[Seventh-order Lean source](../../formal/universal/MockThetaSeventh.lean)

For each function, `denominator_iff` identifies the unique reciprocal.
`summand_at_leading_degree` gives coefficient one at the numerator
exponent. In the common indexing, the first $K$ summands suffice for degree
$d<K^2$ in $\mathcal F_0$, $d<(K+1)^2$ in $\mathcal F_1$, and
$d<K(K+1)$ in $\mathcal F_2$. The `coeff_stable` theorem proves all
three cutoffs.

The named coefficient functions `f0Coeff`, `f1Coeff`, and `f2Coeff` feed
`degreePacket`, `weightedPacket`, and `cylinder`. Summation over the finer
residues reconstructs each coarse packet, and a cylinder is constant on
points with the same selected coordinate. For a certified $b$-root $z$, an
admitted target query at primary $M$ and coupled-anchor resolution $H$ gives
$b\mid MH$. The theorem `from_coupled_anchors` evaluates the coefficient
truncation $\mathcal F_{j,N}(tz)$ from the complete weighted packets at
period $MH$. The bound $N$ counts coefficient degrees.
[Proofs and hypotheses](../../formal/universal/MockThetaSeventh.lean)

## Independent coefficient checks

The finite integer oracle expands each reciprocal factor
$(1-q^j)^{-1}=1+q^j+q^{2j}+\cdots$ up to the required degree, convolves
the arrays, then shifts by the numerator exponent. This checks each named
coefficient through degree 40, with degree-40 coefficients $16,31,39$ for $\mathcal F_0,\mathcal F_1,\mathcal F_2$ respectively.

Garvan's three relations involve coefficients after multiplication by the
Euler product. With
$g_j(d)=[q^d]\prod_{k\ge1}(1-q^k)\mathcal F_j(q)$, they read

$$
g_0(25n+8)=g_2(n),\qquad
g_1(25n+1)=g_0(n),\qquad
g_2(25n-3)=-g_1(n).
$$

Through degree $D$ only the factors with $k\le D$ contribute. The smoke
test checks $n=0,\ldots,4$ in the first two equalities and $n=1,\ldots,4$
in the third, where both indices are nonnegative. These 14 comparisons
reach Euler-weighted degree 108. Garvan proves the full identities.
[Garvan, eqs. (1.6)–(1.8), pp. 3–4](https://arxiv.org/pdf/1907.04803#page=3)

The execution passed **1,819 seventh-order assertions**. Of these, 1,206
exercise named coefficients and their observation APIs, 599 check initial
summands and cutoff boundaries, and 14 check the Euler-weighted identities.
Together the three original groups contribute all **17 named series**. The
full audit compiled 299 declarations, including 17 in `MockThetaSeventh`.
Infinite analytic limits and modular transformation laws remain separate
proof obligations.
[Seventh-order execution](../../evidence/current/profinite-mock-theta/seventh-smoke.log)
· [Smoke program](../../formal/universal/SeventhSmoke.lean)
· [Proof audit](../../evidence/current/profinite-mock-theta/verification.json)
