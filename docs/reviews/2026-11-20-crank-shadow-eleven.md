# Partition crank characters and the CRAM shadow coordinate at eleven

For each partition $\lambda$ of a fixed size $n$, let $s(\lambda)$ be its
signed rank or crank. The new finite construction observes $s(\lambda)\bmod
11$ and counts how many partitions occupy each of the eleven classes. In the
S6 profile, projecting the statistic's primary coordinate modulo 11 gives
exactly this class. Section 6 of the project's profinite-bridge paper
introduced the size-six example and its finite Fourier interpretation.
[Profinite bridge, §6](../../foundations/profinite_bridge/2026-11-20/profinite_bridge/The_Profinite_Bridge_Revised.md#6-the-handoff-at-eleven-through-finite-fourier-analysis)

## The partitions and the eleven counts

`partitions n` enumerates all weakly decreasing lists of positive parts
with sum $n$, each exactly once. Dyson's rank is the largest part minus the
number of parts. For the Andrews–Garvan crank, write $u$ for the number of
ones. A partition with $u=0$ has crank equal to its largest part. For $u>0$,
the crank is the number of parts strictly larger than $u$, minus $u$.
The implementation assigns rank and crank zero to the empty partition.
The singleton $[1]$ has rank zero and ordinary crank $-1$.
[Partition definitions and proofs](../../formal/universal/PartitionCrank11.lean)
· [Andrews and Garvan, *Dyson's Crank of a Partition*](https://doi.org/10.1090/S0273-0979-1988-15637-6)

Lean proves both histograms at size six. The bins occur in residue order
$0,1,\ldots,10$.

| Statistic on the 11 partitions of six | Histogram |
|---|---|
| Rank | $1,2,1,1,0,1,1,0,1,1,2$ |
| Crank | $1,1,1,1,1,1,1,1,1,1,1$ |

The executable also compares the enumerated crank bins with an independent
dynamic program that counts part multiplicities. At sizes $6,17,28,39$, the
eleven bins contain $1,27,338,2835$ partitions apiece, respectively.
Andrews and Garvan give the general equidistribution for sizes $11k+6$.
[Independent count](../../formal/universal/CrankShadowSmoke.lean)
· [Andrews–Garvan](https://doi.org/10.1090/S0273-0979-1988-15637-6)

## Integer counts and finite-field characters

For counts $h_0,\ldots,h_{10}$ write $H(X)=\sum_{r=0}^{10}h_rX^r$. Reducing
by $\Phi_{11}(X)=1+X+\cdots+X^{10}$ leaves coefficients $h_r-h_{10}$ for
$0\le r<10$. Lean proves that all ten **integer** differences vanish if and
only if all eleven bins have equal counts. It also proves the evaluation
formula at every ring element $z$ with $\Phi_{11}(z)=0$. Grouping partitions
by their signed statistic class preserves the sum for every partition list.
When $z^{11}=1$, `statistic_character_add` proves that adding signed statistics
multiplies their character values. At size six, `crank_six_vanishes` proves
crank cancellation at every root of $\Phi_{11}$, and `rank_six_reduced_witness`
gives the nonzero integer difference $h_4-h_{10}=0-2=-2$ for rank.
[Character theorems](../../formal/universal/CrankCharacter11.lean)

In $\mathbb F_{23}$, $z=2$ has order 11. At size six the paired values of the
rank histogram at $z^j$, for $j=0,\ldots,10$, are
$11,8,22,20,2,17,17,2,20,22,8$. The crank values are 11 at $j=0$ and zero
at the ten nontrivial characters. Together the ten nontrivial field characters
detect departure from uniformity modulo 23. Exact uniformity uses the integer
criterion above. At size six, weighting each partition by
$z^6$ would give 14 in the field, while weighting it by its crank class gives
zero. [Finite-field checks](../../formal/universal/CrankShadowSmoke.lean)

## What the mod-11 reading observes

| Source and evidence | Result |
|---|---|
| Signed statistic $s$ supplied as a diagonal source, using the full mod-11 coordinate or the S6 coordinate $s\bmod30030$ | Directly yields $s\bmod11$ because $11\mid30030$ |
| S8 payload $P=881790=2\cdot3\cdot5\cdot7\cdot13\cdot17\cdot19$, transition $Y=X+Ps$, readings $c=X\bmod11$, $w=Y\bmod11$ | $7(w-c)\bmod11=s\bmod11$, using $7P\equiv1\pmod{11}$ |
| S8 source $s$ itself, chart $c=(s\bmod P)\bmod11$, shadow $w=s\bmod11$ | $w$ is the statistic class. The paired query $7(w-c)\bmod11$ gives $\lfloor s/P\rfloor\bmod11$ |

In the transition row, the theorem assumes the specified step and the two
corresponding readings. An implementation must supply the source, phase,
operation, and epoch binding. The theorem `s8_crank_pairing` applies this
readout to every entry of an arbitrary finite partition list. The pinned Rust
`verify_successor` enforces a public nonnegative increment bound and a capacity
bound. The signed Lean result proves the residue identity over the integers.
For the quotient row, a public width-eleven interval
containing $\lfloor s/P\rfloor$ determines its exact signed value. Sources
separated by $11P$ have the same pair of residue readings and quotients
differing by 11. The S8 profile and the S6 primary use different payloads.
[Profile and observation theorems](../../formal/universal/CrankShadow11.lean)
· [NINE65 S8 implementation, pinned lines 36–83](https://github.com/Skyelabz210/NINE65_v7/blob/64c1c89b191093dc12cf81b87da5fb1a02c46dc1/crates/cram-core/src/phase_lock.rs#L36-L83)
· [Machine contract](../ARCHITECTURE.md)

## Size weights from the seventh-order series

For $j=0,1,2$ let $a_j(n)=[q^n]\mathcal F_j(q)$ and let $C_r(n)$ count
partitions of $n$ with crank class $r$. The new finite bivariate polynomial is

$$
B_{j,N}(t,z)=\sum_{n<N}a_j(n)t^n\sum_{r=0}^{10}C_r(n)z^r.
$$

The theorem `seventh_crank_pairing` proves that summing the weighted bins
by $r$ gives the same value as summing directly over each size and its
partitions. It holds for all $t,z$ in a commutative ring. When $z^{11}=1$,
$z^r$ is the statistic character and $t^n$ weights partition size.
The theorem `seventh_crank_from_s8` evaluates the same polynomial from the
paired chart and shadow readings for every $j$ and every finite cutoff $N$,
assuming the affine crank step and authentic readings for each retained
partition. For $\mathcal F_2$ with $N=8$, $t=3$, and $z=2$ in
$\mathbb F_{23}$, the dynamic program, histogram, direct partition sum, and
paired S8 readings all give **15**. Identifying this newly defined polynomial
with a classical mock theta identity or an analytic shadow would require
additional theorems.
[Named pairing](../../formal/universal/CrankCharacter11.lean)
· [Seventh-order coefficient source](../../formal/universal/MockThetaSeventh.lean)

For comparison, the classical rank generating function satisfies $R(-1;q)=f(q)$
for Ramanujan's third-order $f$. The smoke program independently sums one for
even signed rank and minus one for odd signed rank at each size $0$ through
$40$, matching the named Lean coefficient at every checked degree. This uses
parity of the original rank. Reducing the rank modulo 11 can change its parity.
The all-degree identity is a literature result.
[Rank specialization, §6](../../foundations/profinite_bridge/2026-11-20/profinite_bridge/The_Profinite_Bridge_Revised.md#6-the-handoff-at-eleven-through-finite-fourier-analysis)
· [Ono, Arizona Winter School notes](https://swc-math.github.io/aws/2013/2013OnoNotes.pdf)

The new suite passed **247 exact assertions**. It includes 43 rank-parity
and boundary checks, 88 crank-bin counts, 57 finite Fourier checks, 45 signed
S6 and S8 observation checks and controls, and 14 size-weighted checks.
[Crank execution log](../../evidence/current/profinite-mock-theta/crank-shadow-smoke.log)
· [Source and compiler receipt](../../evidence/current/profinite-mock-theta/execution.json)
