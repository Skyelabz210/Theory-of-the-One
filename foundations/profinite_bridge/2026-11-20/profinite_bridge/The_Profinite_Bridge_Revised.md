---
title: The Profinite Bridge
subtitle: CRAM observation spaces mock theta series and exact character requirements
author: Research synthesis for Anthony Diaz
date: November 20 2026
---

# Abstract

Ramanujan's original seventeen mock theta examples fall into families of orders three, five, and seven: four, ten, and three examples respectively. These family labels belong to CRAM's selected safe basis $S=\{2,3,5,7,11,13\}$. This historical alignment motivates a connection, while the connection itself requires explicit maps between arithmetic observations and analytic functions.

This paper constructs two such maps. First, for a primary period $M$ and target modulus $b$, the reduced winding requirement $h_b=b/\gcd(M,b)$ is exactly the order of the target character along the direction forgotten by reduction modulo $M$. Second, for an analytic series $f(q)=\sum a_nq^n$ and $0<t<1$, the coefficient measure $\nu_t=\sum a_nt^n\delta_{\iota(n)}$ on an appropriate profinite observation space has Fourier transform $\widehat{\nu_t}(\zeta)=f(t\zeta)$. Finite residue-class sums provide exact versions of this transform.

The observation space depends on the periods actually supplied. The completion using only $S$-smooth moduli is $\prod_{p\in S}\mathbb Z_p$. Authentic outside-prime sisters contribute additional observations. If primary refinements and the full affine star family are available compatibly, their periods are cofinal among all positive integers, and the resulting completion is $\widehat{\mathbb Z}$. This conditional construction preserves the fixed primary basis.

The paper also repairs the proposed StarLift section, distinguishes finite CRT rank from source winding, and gives a concrete Fourier interpretation of the rank-to-crank handoff modulo eleven. A correspondence between analytic mock modular shadows and CRAM observation obstructions remains unproved; the generic claim requires additional definitions and cannot follow from Pontryagin duality alone.

# 1 Scope and historical alignment

This paper develops a mathematical model for authentic, compatible CRAM observations. It preserves the selected primary basis, dependent sister relationships, and quotient information derived on demand. The semantic identity $X=r+MK$ will be used in proofs; it does not prescribe storing $X$ or $K$ as a persistent scalar state or reconstructing them in the runtime.

## The original seventeen examples

Ramanujan's letter to Hardy of January 12, 1920 contains the following grouping. [1]

| Family order | Number of examples |
|:---:|:---:|
| 3 | 4 |
| 5 | 10 |
| 7 | 3 |
| Total | 17 |

Thus the set of family labels is exactly $\{3,5,7\}\subset S$. This observation belongs in the motivation. A family order, the multiplicative order of a root of unity, a modular transformation level, and a machine observation modulus are nevertheless different mathematical data. A theorem must specify any proposed identification among them.

For example, the classical third-order function $f$ has a radial-limit theorem at every primitive even-order root. Choosing a primitive root of order $34$ invokes prime $17$, although the function remains third order. The root order is therefore not confined to the prime factors of the family label or to $S$. [2, Theorem 1.1]

The particular safe basis may have additional architectural roles. Its selection does not follow from the historical grouping alone.

## Four levels of assertion

We distinguish standard mathematical structure, deductions proved here, inspected CRAM source contracts, and proposed correspondence. The profinite duality is standard. The arithmetic and Fourier constructions below are consequences of that framework with explicit proofs, without a claim of mathematical novelty. A production observation constructor must additionally satisfy the source and operation laws required by the architecture. An interpretation connecting its operation to a mock modular shadow requires further work.

# 2 The completion follows the observations

Let $\mathcal L$ be a directed family of positive integer periods, ordered by divisibility. Finite combinations of authentic observations have their compatible-tuple period equal to the least common multiple of their moduli. We therefore include these joint periods in $\mathcal L$.

Define the inverse limit along the canonical reduction maps

$$
G_{\mathcal L}=\lim_{L\in\mathcal L}\mathbb Z/L\mathbb Z.
$$

The reduction maps express agreement between observations of the same source. Specifying moduli without these agreement maps is insufficient to define the intended inverse system.

## Characters and observable targets

**Theorem 1.** With the usual reduction maps,

$$
\widehat{G_{\mathcal L}}\cong\bigcup_{L\in\mathcal L}\mu_L.
$$

Here $\mu_L$ is the finite group of $L$th roots of unity, and the union is given the discrete dual topology. The pairing is

$$
\langle\zeta,x\rangle=\zeta^{x_L}
\qquad
\text{when }\operatorname{ord}(\zeta)\mid L.
$$

**Proof.** The dual of $\mathbb Z/L\mathbb Z$ is $\mu_L$. Pullback along reduction embeds these character groups compatibly. Every continuous character of a profinite abelian group has finite image: its image is a profinite closed subgroup of the circle, and hence is a finite cyclic group. Its open kernel contains the kernel of some finite-level projection. Therefore it factors through an admitted finite quotient. This proves the asserted union and pairing. The compact and discrete duality framework is standard. [3]

**Corollary 1.** Ordinary integer reduction modulo $b$ extends to a continuous query on $G_{\mathcal L}$ if and only if

$$
b\mid L\quad\text{for some }L\in\mathcal L.
$$

Indeed the primitive character $n\mapsto e^{2\pi in/b}$ has order $b$ and belongs to the displayed dual exactly under this divisibility condition. A continuous extension from the dense integer image is unique. This criterion concerns unbounded integers; an additional range promise can restrict the admissible domain.

## The primary completion

For $P=30030$ and all $S$-smooth moduli,

$$
R_S=\lim_{M\in\langle S\rangle}\mathbb Z/M\mathbb Z
\cong\prod_{p\in S}\mathbb Z_p.
$$

The powers $P^n$ already form a cofinal family among these moduli. CRT gives the product decomposition, and

$$
\widehat{R_S}\cong\mu_S
\cong\mathbb Z[S^{-1}]/\mathbb Z
\cong\bigoplus_{p\in S}\mathbb Q_p/\mathbb Z_p.
$$

The notation $\mu_S$ means roots whose orders are $S$-smooth. It describes the continuous character spectrum of this specific completion. It does not establish that every authentic CRAM sister observation is already a coordinate of $R_S$.

## Why an outside anchor is additional evidence

Suppose $M$ is divisible by every prime of $S$ and $A=cM\pm1>1$, with integer $c\ge1$. Then $A$ is coprime to every prime of $S$. Multiplication by $A$ is an automorphism of $R_S$. Consequently any additive homomorphism $\phi:R_S\to\mathbb Z/A\mathbb Z$ satisfies

$$
x=Ay\quad\Longrightarrow\quad\phi(x)=A\phi(y)=0.
$$

There is no homomorphism extending ordinary integer reduction modulo $A$. This is stronger than a failure of continuity.

For a concrete illustration,

$$
M=30030,\qquad A=30031=59\cdot509.
$$

In $R_S$, $P^n$ converges to zero, but its integer residues modulo $A$ alternate between $1$ and $-1$. Thus even a continuous extension of that integer query is impossible.

For an arbitrary additional modulus $A$, write

$$
A_S=\prod_{p\in S}p^{v_p(A)},\qquad A_{\mathrm{out}}=A/A_S.
$$

Adding its authentic same-source residue gives the compatible state space

$$
E_A=\{(x,a):x\bmod A_S=a\bmod A_S\}.
$$

By CRT,

$$
E_A\cong R_S\times\mathbb Z/A_{\mathrm{out}}\mathbb Z.
$$

One finite observation adds finite outside information. It does not automatically supply all powers of the newly encountered primes. Nor does setting the extra coordinate to zero generate the original integer's authentic observation. The primary is retained; the source-bound sister contributes information.

## A fixed primary can support the full profinite completion

**Theorem 2.** Keep the finite primary $P$ fixed. Assume additional compatible refinement observations at levels $M=P^n$ are available, together with authentic observations at every star modulus $A=cM+1$, for positive integers $n,c$. Here $M$ denotes a refinement level, not a replacement of the primary. Close their joint observation periods under finite least common multiples. Then the resulting period family is cofinal among all positive integers, and

$$
G_{\mathcal L}\cong\widehat{\mathbb Z},
\qquad
\widehat{G_{\mathcal L}}\cong\mathbb Q/\mathbb Z.
$$

**Proof.** Given $b$, factor only by support:

$$
b=b_Sb_{\mathrm{out}},\qquad
\gcd(b_{\mathrm{out}},P)=1.
$$

Choose $n$ so that $b_S\mid M=P^n$. Since $M$ is a unit modulo $b_{\mathrm{out}}$, choose a positive $c$ satisfying

$$
cM\equiv-1\pmod{b_{\mathrm{out}}}.
$$

If $b_{\mathrm{out}}=1$, any positive $c$ suffices. Then $b_{\mathrm{out}}\mid A=cM+1$, while $b_S\mid M$. Therefore $b\mid MA$. Every finite target is covered at some level, proving cofinality and the resulting completion.

For the root order $34$, one may already take $M=30030$ and $c=2$:

$$
A=60061=17\cdot3533,\qquad 34\mid MA.
$$

This is an example of admitting the outside-prime character through a sister, while retaining the same primary labels. The theorem is conditional on authentic production and compatible refinement. It does not assert that a finite machine stores an infinite family.

If $M$ is held at one finite precision while all star coefficients are allowed, the corresponding limit is instead

$$
\mathbb Z/M\mathbb Z\times\prod_{p\nmid M}\mathbb Z_p.
$$

The primary primes then retain only their existing finite precision. For fixed $M=30030$, no joint period from this star family is divisible by $4$, since every star is odd. The additional power observations are therefore substantive evidence. This distinction identifies exactly which refinement capability is required.

# 3 What StarLift recovers

Let $r$ be the canonical residue of the source modulo $M$, let $a$ be its authentic residue modulo $A$, and assume $\gcd(M,A)=1$. From the semantic decomposition $X=r+MK$,

$$
K\equiv(a-r)M^{-1}\pmod A.
$$

For the star families with integer $c\ge1$ and $A>1$,

$$
\begin{aligned}
A=cM+1&:\quad M^{-1}\equiv-c,\quad K\equiv c(r-a)\pmod A,\\
A=cM-1&:\quad M^{-1}\equiv c,\quad K\equiv c(a-r)\pmod A.
\end{aligned}
$$

Let $k_A$ be this quotient residue in $[0,A)$. Then

$$
r+Mk_A\in[0,MA)
$$

is the unique representative of the compatible observation pair in that window. The identity is an exact readout law; whether a specific implementation evaluates a full representative or only the required target remains an architectural choice.

## Correct section language

A section of $\pi:E\to B$ has direction $s:B\to E$ and obeys $\pi s=\mathrm{id}_B$. The canonical representative map

$$
s:\mathbb Z/MA\mathbb Z\longrightarrow\mathbb Z
$$

is a set section of integer reduction. StarLift can realize this finite representative through its quotient coordinate. It is not a section $R_S\to\mathbb Z/A\mathbb Z$ of the unavailable outside-anchor projection.

The two signs select different affine moduli. They do not exchange the endpoints of a common window. For example, $M=6$ and $X=20$ give $r=2$ and $K=3$. Both the $A=7$ and $A=5$ formulas recover $20$ in their respective windows. At $X=0$, both recover zero. Outside a supplied range, observations at $M$ and $A$ identify $X$ modulo $MA$.

## The exact place for zero and signed one

For $0\le r,s<M$, the nonadditivity of the canonical representative is measured by

$$
\epsilon_+(r,s)=\operatorname{floor}\left(\frac{r+s}{M}\right)\in\{0,1\}.
$$

Subtraction has the borrow correction

$$
\epsilon_-(r,s)=\operatorname{floor}\left(\frac{r-s}{M}\right)\in\{-1,0\}.
$$

For example,

$$
K(X+Y)=K(X)+K(Y)+\epsilon_+(r_X,r_Y).
$$

These are precise carry and borrow laws, or section cocycles. They make the values $0,\pm1$ operationally meaningful. They are not the topological boundary of the integers in their completion.

Basic profinite residue neighborhoods are clopen, so their boundaries are empty. The diagonal integers are dense and have empty interior in $R_S$, so their boundary is all of $R_S$. A finite correction set cannot be identified with either boundary without introducing a different explicitly defined notion.

# 4 Reduced winding is an exact character order

**Theorem 3.** For positive integers $M,b$, put

$$
d=\gcd(M,b),\qquad h_b=b/d.
$$

Along the primary fiber $X=r+MK$, factor out the known primary phase $\zeta_b^r$. The remaining quotient-direction character $K\mapsto(\zeta_b^M)^K$ has exact order $h_b$.

**Proof.** For $\zeta_b=e^{2\pi i/b}$,

$$
\zeta_b^X=\zeta_b^r(\zeta_b^M)^K.
$$

The order of $\zeta_b^M$ is $b/\gcd(M,b)$. Equivalently,

$$
(\zeta_b^M)^K
=\exp\left(\frac{2\pi i(M/d)K}{h_b}\right),
$$

and $\gcd(M/d,h_b)=1$. The target character distinguishes exactly $K$ modulo $h_b$.

It follows immediately that quotient evidence $K\bmod H$, together with the primary residue $r$ or its required target chart, determines $X\bmod b$ for every integer source if and only if

$$
h_b\mid H.
$$

For necessity, $K$ and $K+H$ are indistinguishable to the supplied evidence; their target characters coincide precisely when $b\mid MH$, which is equivalent to $h_b\mid H$. Sufficiency follows from the same formula.

This is the direct dual meaning of the reduced winding theorem: **the required quotient period is the order of the target character on the direction omitted by the primary observation**. The argument does not require a stored integer quotient.

## Exact sequences

With $L=\operatorname{lcm}(M,b)=Mh_b$, the finite observation extension has exact sequence

$$
0\longrightarrow\mathbb Z/h_b\mathbb Z
\xrightarrow{k\mapsto Mk}
\mathbb Z/L\mathbb Z
\xrightarrow{\bmod M}
\mathbb Z/M\mathbb Z
\longrightarrow0.
$$

Its character sequence is

$$
1\longrightarrow\mu_M
\longrightarrow\mu_L
\xrightarrow{\zeta\mapsto\zeta^M}
\mu_{h_b}
\longrightarrow1.
$$

Among the target characters themselves, the already visible subgroup is

$$
\mu_b\cap\mu_M=\mu_d,
$$

and restriction to the quotient direction gives

$$
1\longrightarrow\mu_d
\longrightarrow\mu_b
\xrightarrow{\zeta\mapsto\zeta^M}
\mu_{h_b}
\longrightarrow1.
$$

These sequences formalize information supplied and information still required. Their existence does not identify any analytic modular obstruction with that arithmetic requirement.

## Finite evidence and infinite uniqueness

A single level gives $X$ only modulo its period. The entire coherent state in $R_S$ distinguishes any two ordinary integers: if their difference is divisible by every $P^n$, that difference is zero.

Most completion points are not diagonal integers. For instance, a point whose $2$-adic coordinate is zero and whose $3$-adic coordinate is one cannot be an ordinary integer. Moreover, uniqueness from an infinite object does not make an outside-prime query continuous or computable from a finite prefix. These are three separate questions: existence of an integer representative, uniqueness if it exists, and finite observability of a specified query.

# 5 A Fourier bridge for the series themselves

A pairing between a group and its characters does not, by itself, put a mock theta function in either group. Its coefficients supply the missing object.

Let $f(q)=\sum_{n\ge0}a_nq^n$ be analytic on the open unit disc. Let $\iota(n)$ be the diagonal image of $n$ in an observation completion $G_{\mathcal L}$. For $0<t<1$, define the complex measure

$$
\nu_t=\sum_{n\ge0}a_nt^n\delta_{\iota(n)}.
$$

Absolute convergence of the Taylor series at radius $t$ gives a finite total variation bound. Use the positive-exponent Fourier convention.

**Theorem 4.** For every admitted root of unity $\zeta\in\widehat{G_{\mathcal L}}$,

$$
\widehat{\nu_t}(\zeta)
=\int_{G_{\mathcal L}}\langle\zeta,x\rangle\,d\nu_t(x)
=\sum_{n\ge0}a_nt^n\zeta^n
=f(t\zeta).
$$

**Proof.** The character has modulus one. Absolute convergence permits evaluation term by term, and its value at $\iota(n)$ is $\zeta^n$.

This is a literal transform connection. It uses the coefficients of the series and the authentic residue interpretation of their integer index. It applies to every analytic power series, including the original mock theta examples; its existence alone does not characterize mock modularity.

## Finite residue classes

At an admitted period $L$, define

$$
C_{L,r}(t)=\sum_{\substack{n\ge0\\n\equiv r\pmod L}}a_nt^n
\qquad (0\le r<L).
$$

Then

$$
f(t\zeta_L^j)=\sum_{r=0}^{L-1}C_{L,r}(t)\zeta_L^{jr},
$$

and finite Fourier inversion gives

$$
C_{L,r}(t)=\frac1L\sum_{j=0}^{L-1}
f(t\zeta_L^j)\zeta_L^{-jr}.
$$

If $L\mid L'$, the coefficient packets satisfy the refinement law

$$
C_{L,r}(t)=\sum_{\substack{0\le s<L'\\s\equiv r\pmod L}}C_{L',s}(t).
$$

Thus the finite transforms commute with the same refinement maps that define the profinite space. This coefficient encoding is faithful even on the primary completion. For fixed $r$ and $P^n>r$, the absolute tail bound gives

$$
\lim_{n\to\infty}C_{P^n,r}(t)=a_rt^r.
$$

The restricted character spectrum limits the directly admitted finite root orders; it does not prevent this particular infinite coefficient encoding from retaining every coefficient.

For finite coefficient truncations, one may retain a formal variable $T$ and use polynomials

$$
C^{(N)}_{L,r}(T)=
\sum_{\substack{0\le n\le N\\n\equiv r\pmod L}}a_nT^n.
$$

Their Fourier evaluations lie in a cyclotomic coefficient extension. This supplies an exact algebraic formulation before numerical radial evaluation. It does not require floating point inside the residue representation.

## What happens at the unit circle

The expression $f(\zeta)$ must not be assumed finite. The exact transform above uses $t<1$. The mock theta question concerns the limit $t\uparrow1$, often after subtracting a root-dependent modular term.

When $\iota$ is injective, as for $R_S$ and $\widehat{\mathbb Z}$,

$$
\|\nu_t\|_{\mathrm{TV}}=\sum_{n\ge0}|a_n|t^n.
$$

A finite-measure weak-star limit as $t\uparrow1$ therefore requires summable coefficients; conversely summability gives convergence in total variation. Necessity follows from uniform boundedness of a weak-star convergent family and monotone convergence of the displayed positive sum. Analyticity in the disc alone supplies neither property.

A regularized limit on selected characters can exist even when the measure norms diverge. Any distributional or regularized boundary object must be defined with its test functions and subtraction law. Failure of a finite-measure limit is not itself a mock modular shadow: an ordinary theta series can already have nonsummable coefficients.

# 6 The handoff at eleven through finite Fourier analysis

The rank generating function is

$$
R(w;q)=\sum_{n\ge0}\sum_{m\in\mathbb Z}N(m,n)w^mq^n,
$$

where $N(m,n)$ counts partitions of $n$ with rank $m$. Its classical specialization

$$
R(-1;q)=f(q)
$$

is Ramanujan's third-order example. Here $w=-1$ is a character of order two, while $f$ has family order three. This is an explicit relation between different orders, with a specified map. [4]

For fixed $n$, let $N_r(n)$ count partitions whose rank is $r$ modulo eleven. The finite character values are

$$
\mathcal R_j(n)=\sum_{r=0}^{10}N_r(n)\zeta_{11}^{jr}.
$$

Fourier inversion recovers every $N_r(n)$. In particular,

$$
N_0(n)=\cdots=N_{10}(n)
\quad\Longleftrightarrow\quad
\mathcal R_j(n)=0\ \text{for }j=1,\ldots,10.
$$

The crank statistic has an analogous transform. It is the change in the statistic's distribution that makes the eleven-congruence handoff effective. The Fourier pairing remains exact for both statistics.

As an explicit small check, the eleven partitions of $6$ have rank counts, in residue order $0,\ldots,10$,

$$
(1,2,1,1,0,1,1,0,1,1,2),
$$

whereas their crank counts are

$$
(1,1,1,1,1,1,1,1,1,1,1).
$$

Here rank is largest part minus number of parts. If a partition has no ones, its crank is its largest part; otherwise its crank is the number of parts larger than the number of ones, minus the number of ones. Enumeration reproduces the two vectors. This finite example illustrates the distinction; the general crank theorem requires its established combinatorial theory.

The Fourier variable here is $w$, which indexes the partition statistic. The radial variable $q$ indexes partition size. A CRAM representation must state which integer each lane observes. The two axes cannot be silently identified.

Published work already relates rank, crank, and regularized mock theta radial limits. [2] That literature provides a concrete analytic route for the proposed bridge. It does not equate the project's designated shadow-eleven role with a weight-three-halves analytic shadow.

# 7 The finite CRT correction packet

The inspected CRAM packet uses normalized coefficients. For pairwise coprime $m_i>1$, let

$$
M=\prod_i m_i,\qquad M_i=M/m_i,\qquad
\xi_i=(x_iM_i^{-1})\bmod m_i.
$$

Define the normalized sum $T$ and rank $\alpha$ by

$$
T=\sum_i\xi_iM_i=r+\alpha M,\qquad 0\le r<M.
$$

For the source $X=r+MK$ and authentic unit anchor $A$, set

$$
\gamma=((X\bmod A-T\bmod A)M^{-1})\bmod A.
$$

Then

$$
\gamma\equiv K-\alpha\pmod A,\qquad
K\equiv\alpha+\gamma\pmod A.
$$

The symbol $\gamma$ is used here to avoid confusing this packet correction with the star coefficient $c$.

The source packet tested 18,000 cases across bases of six, seven, and eight lanes, two anchor choices per base, and sources in $[0,MA)$. A targeted replay reproduced zero violations of this identity and candidate containment. The tested candidate set was the translated interval $\{(\gamma+a)\bmod A:0\le a<k\}$. Its sizes six, seven, and eight were consequences of that construction. [8]

## The sharper selected-basis bound

The normalized coefficients are independent and satisfy $0\le\xi_i<m_i$, so

$$
\alpha_{\max}=
\operatorname{floor}\left(\sum_i\frac{m_i-1}{m_i}\right).
$$

For the selected six prime moduli,

$$
\alpha_{\max}=
\operatorname{floor}\left(6-\frac{40361}{30030}\right)=4.
$$

Every rank from zero through four occurs. An exhaustive enumeration of the 30,030 canonical states gave:

| Normalized rank | Number of states |
|:---:|---:|
| 0 | 738 |
| 1 | 8862 |
| 2 | 15420 |
| 3 | 4847 |
| 4 | 163 |

Thus the sharp candidate set from this bound is $\{\gamma,\ldots,\gamma+4\}$ modulo $A$. The symmetric set $[-4,4]$ describes differences between possible ranks, not the candidate set itself.

The complete primary tuple determines $\alpha$ mathematically; leaving it unevaluated is a computational choice. This rank is distinct from source winding $K$ and from a rank computed using unnormalized CRT terms. It is also distinct from the topological boundary of a completion. The source ledger treats the sharp rank theorem as ordinary mathematical work awaiting its own Lean formalization. [8]

# 8 The analytic obstruction and the remaining conjecture

For the normalized original mock theta examples, established work rules out a single weakly holomorphic modular form that removes the singular behavior at every root of unity. Their modern description uses a nonholomorphic completion governed by a unary theta shadow. [5] Rhoades shows that the broad historical and modern definitions are not equivalent; this does not invalidate either description of the original examples. [6]

The all-roots statement cannot automatically be restricted to $\mu_S$. Failure of one subtraction on a larger set does not imply failure on each specified subset. If the observation family is cofinal as in Theorem 2, all finite root orders are available. If only $R_S$ is used, an obstruction theorem on that restricted spectrum needs a separate argument.

Local modular subtraction, the analytic shadow, arithmetic target resolution, and convergence of the coefficient measures are different constructions. Current radial-limit theory already supplies substantial results on the first of them. [7]

## Why duality alone cannot identify the obstructions

The quantity $h_b$ depends on $M$ and $b$, not on a chosen function $f$. Keep a genuine mock theta function with nonzero analytic shadow fixed, and choose $b\mid M$. Then $h_b=1$, so the primary already determines the target, while the function's analytic shadow remains nonzero. Conversely, an ordinary modular theta function can have zero mock shadow while an arbitrary outside target still requires $h_b>1$.

Therefore there is no universal vanishing-preserving identification of analytic shadow with reduced winding requirement based on the pairing alone. A tailored correspondence must first specify how $f$, its coefficients or statistics, the machine state, and the target family are connected.

## A precise research question

Choose one original mock theta function, a declared normalization, and a representation of its coefficient or statistic packets by authentic coupled observations. Use Theorem 4 as the transform. Define the modular transformation defect or regularized radial defect on the analytic side. Define a corresponding operator or compatibility defect on the observation side.

The research objective is then to prove that the transform intertwines the two specified defects and their resolution procedures. A successful result must state the domains, operators, limiting process, and preserved invariant. Matching the words local, global, shadow, or boundary does not supply those maps.

Theorem 3 already establishes the arithmetic character requirement. Theorem 4 already establishes a transform of the series. The additional mock-specific result must explain what the modular structure contributes beyond these general facts.

# 9 Prime roles and the proposed significance of twenty three

The source reconciliation gives the selected primary role assignments: parking or parity at two, fabric at three, surface at five, bridge at seven, shadow or navigation at eleven, and boundary at thirteen. It requires explicit source, phase, operator, and signature-preservation laws before transferring those roles to sister configurations. It also describes outside-prime docking without replacing the primary. [9]

Neither profinite duality nor product capacity proves that thirteen is dispensable, uniquely necessary, or the weakest role. An operational characterization must specify the invariant that thirteen supplies and compare admitted alternatives under the same contract.

The proposal compares the sets $\{5,7,11\}$ and $\{2,3,5,7,23,691\}$. Even accepting these sets for the intended partition and tau criteria, they already disagree at eleven; a literal comparison also differs at two and three. A claim restricted to primes after thirteen must say so and define which tau property is intended. These sets do not prove that twenty three is the first structural or dynamical boundary.

A finite multiplicative orbit modulo $667=23\cdot29$ can have a valid checked period without establishing a universal boundary for mock theta behavior. Root orders involving seventeen already arise in the third-order radial theory. To make twenty three operationally special, specify the exact CRAM instruction that consumes its invariant and demonstrate what it enables.

No change to the selected primary is required by these observations. Theorems 1 and 2 describe the additional character spectrum supplied by authentic dependent observations.

# 10 What this formulation enables

The arithmetic character theorem gives a query admission rule: an instruction requiring period $b$ can be checked against the actual joint observation period. Its reduced requirement is computed on the omitted quotient direction. Shared-factor observations fit the same criterion through least common multiples.

The coefficient transform supplies a representation for exact generating-function residue packets, finite cyclotomic evaluations, and compatible refinement. It can be used for partition statistics and other analytic series whose coefficients have meaningful residue structure. Such uses require their own source and operation contracts, but the Fourier identities do not depend on mock modularity.

The conditional cofinality theorem explains how a fixed finite primary vocabulary can support an unbounded family of finite observations. This concerns extensibility of the representation, not infinite storage at a finite step. A source-preserving constructor for each requested precision is the relevant implementation obligation.

The analytic opportunity is to compare modular transformation laws with specific transformations of these compatible packets. A result of that kind would add mock-specific structure to the general arithmetic bridge. It is the next theorem to formulate, rather than an already established consequence of the terminology.

# 11 Verification and evidence boundary

| Result | Evidence status |
|---|---|
| Original seventeen grouped by orders three five and seven | Original letter inspected |
| Primary completion and Pontryagin pairing | Standard theory with explicit construction |
| Outside-anchor obstruction | Algebraic proof and concrete sequence |
| Cofinality of full refined star family | Conditional theorem proved here |
| Reduced winding as character order | Exact proof and finite character sequences |
| Coefficient measure and Fourier identities | Exact proof for radius less than one |
| Rank and crank counts for partitions of six | Fresh finite enumeration |
| Packet identity in 18000 cases | Source inspection and targeted replay |
| S6 normalized rank distribution | Exhaustive enumeration of 30030 states |
| Shadow correspondence | Open and requiring additional maps |
| Production realization of the full inverse system | Not established by this paper |

The inspected Lean star inverse declaration covers the plus family. The minus identity follows directly from $cM=A+1$, but it should not be attributed to that plus-only declaration without another inspected formal proof. No fresh Lean or Rust build was performed for this revision. Historical benchmark counts and earlier compilation receipts are not new verification of the profinite or analytic claims.

The proofs in this paper use semantic scalar decompositions to state correctness. They do not authorize replacing the chosen residue-native operations with scalar reconstruction or retaining winding as a persistent ledger.

# 12 Revised thesis

Ramanujan's seventeen original mock theta functions are grouped by the safe-basis family labels three, five, and seven. Their relation to CRAM can be expressed through compatible residue observations and character evaluation. The actual observation periods determine the profinite space; its characters specify the finite root orders that can be observed. The primary completion has the $S$-smooth spectrum, while a compatible, authentic refined star family can support the full torsion spectrum without changing the primary.

On a finite primary fiber, the required winding period is exactly the order of the target character. For a mock theta series inside the unit disc, its root-twisted evaluations are Fourier transforms of coefficient measures on the observation space. These are established mathematical bridges with explicit maps.

The analytic shadow, regularized radial behavior, and the designated shadow-eleven role require an additional operation-level correspondence. That correspondence remains a research objective. The revised framework supplies concrete objects on both sides and identifies the theorem still needed.

# References

[1] S. Ramanujan. Letter to G. H. Hardy, January 12, 1920. Trinity College Library, Add. MS a/94/14. [Transcription of the letter](https://www.imsc.res.in/~rao/ramanujan/newnow/lastletter.pdf).

[2] A. Folsom, K. Ono, and R. C. Rhoades. Mock Theta Functions and Quantum Modular Forms. Forum of Mathematics, Pi 1, e2, 2013. DOI 10.1017/fmp.2013.3. Especially Theorems 1.1 and 1.2. [Author PDF](https://afolsom.people.amherst.edu/FolsomOnoRhoades-ForumPi.pdf).

[3] R. Sharifi. Iwasawa Theory, Chapter 2, Section 2.5, Pontryagin duality. [Author lecture notes](https://www.math.ucla.edu/~sharifi/notes/iwasawa-ch02.html).

[4] K. Ono. Harmonic Maass Forms, Mock Modular Forms, and Quantum Modular Forms. Arizona Winter School lecture notes, 2013. See the rank generating function and its specialization at minus one. [Lecture notes](https://swc-math.github.io/aws/2013/2013OnoNotes.pdf).

[5] M. Griffin, K. Ono, and L. Rolen. Ramanujan's Mock Theta Functions. Proceedings of the National Academy of Sciences 110, 5765-5768, 2013. Especially Theorem 1.1 and Corollary 1.2. [Author PDF](https://math.vanderbilt.edu/rolenl/rama_mock_live.pdf).

[6] R. C. Rhoades. On Ramanujan's Definition of Mock Theta Function. Proceedings of the National Academy of Sciences 110, 7592-7594, 2013. DOI 10.1073/pnas.1301046110. [Full text](https://pmc.ncbi.nlm.nih.gov/articles/PMC3651474/).

[7] K. Bringmann and L. Rolen. Radial Limits of Mock Theta Functions. Author manuscript dated June 26, 2015. [Author PDF](https://www.mi.uni-koeln.de/Bringmann/mock_definition_publish.pdf).

[8] NINE65_v7. CRAM Core Lock, November 17, 2026. Pinned revision 64c1c89b191093dc12cf81b87da5fb1a02c46dc1. [Core analysis](https://github.com/Skyelabz210/NINE65_v7/blob/64c1c89b191093dc12cf81b87da5fb1a02c46dc1/docs/proofs/cram/collection/CRAM%20Core%20Lock%202026-11-17/ANALYSIS.md), [torus review](https://github.com/Skyelabz210/NINE65_v7/blob/64c1c89b191093dc12cf81b87da5fb1a02c46dc1/docs/proofs/cram/collection/CRAM%20Core%20Lock%202026-11-17/evidence/torus-review/report.md), [experiment](https://github.com/Skyelabz210/NINE65_v7/blob/64c1c89b191093dc12cf81b87da5fb1a02c46dc1/docs/proofs/cram/collection/CRAM%20Core%20Lock%202026-11-17/evidence/torus-review/Torus_Fiber_Checks_Reproduction_2026-11-17/torus_fiber_checks/carry_questions.py), and [archived output](https://github.com/Skyelabz210/NINE65_v7/blob/64c1c89b191093dc12cf81b87da5fb1a02c46dc1/docs/proofs/cram/collection/CRAM%20Core%20Lock%202026-11-17/evidence/torus-review/Torus_Fiber_Checks_Reproduction_2026-11-17/torus_fiber_checks/carry_questions_output.txt).

[9] NINE65_v7. Prime Family reconciliation, November 17, 2026. Same pinned revision as [8]. [Role-preserving transport and the fixed primary](https://github.com/Skyelabz210/NINE65_v7/blob/64c1c89b191093dc12cf81b87da5fb1a02c46dc1/docs/proofs/cram/PRIME_FAMILY_RECONCILIATION_2026-11-17.md).

[10] N. Elkies. Outline of Pontrjagin Duality. Harvard Mathematics lecture notes. Standard examples include the duality of the discrete integers and the circle. [Lecture notes](https://people.math.harvard.edu/~elkies/M55b.02/pontrjagin.html).

# Appendix Topological conventions

The unit-circle boundary of the complex disc is $\mathbb T=\mathbb R/\mathbb Z$. Its torsion subgroup is $\mathbb Q/\mathbb Z$, represented by all roots of unity. The torsion subgroup is dense in the circle and is not the whole circle.

The same underlying root group $\mu_S$ has different topologies in different roles. As the Pontryagin dual of compact $R_S$, it is discrete. As a subset of the complex circle, it is dense and not discrete. There is no contradiction.

The usual topology on $\mathbb Z$, inherited from $\mathbb R$, is discrete, and $\widehat{\mathbb Z_{\mathrm{disc}}}=\mathbb T$. Restricting characters from $R_S$ to these integers embeds $\mu_S$ into $\mathbb T$. This is an injection, not a quotient of the form $\mu_S\to\mu_\infty/\mathbb Z$. [10]

The integers with the topology induced by $R_S$ are instead dense and precompact. Their continuous characters are exactly the $S$-supported torsion characters. Stating the chosen topology resolves the apparent conflict; no prohibition on dualizing the integers is needed.

For $M>1$ supported on $S$, the exact sequence

$$
0\longrightarrow R_S\xrightarrow{\times M}R_S
\longrightarrow\mathbb Z/M\mathbb Z\longrightarrow0
$$

has continuous set sections but no additive section, since $R_S$ is torsion-free. This supplies a legitimate profinite section statement. It is separate from the finite StarLift observation law and its choice of canonical representative.

