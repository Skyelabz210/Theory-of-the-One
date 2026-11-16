# Theory of the One: from Euclid's definitions to exact computation

## Scope of the research program

Theory of the One develops the consequences of Euclid's account of unity, number, and measurement for exact computation. Its method begins with the definitions as written and proceeds through explicit mathematical derivations. CRAM is the configurable machine architecture developed from that foundation. The mathematics can support several implementations and applications.

Residue number systems are an established area of computer arithmetic. Publisher sources explicitly treat their mathematical fundamentals, carry-free parallel operations, comparison, sign, scaling and division. The repository should engage that literature at the level of actual representation and operation contracts.

Euclid Book VII begins with units and multitudes, then measurement, divisibility and related arithmetic. Its first two propositions use repeated subtraction and remainders to establish common-measure results. The research follows these statements into explicit consequences for exact computation. Modern residue notation supplies a language for those derivations. The [foundational chain](EUCLID_TO_CRAM.md) identifies the source statements, mathematical definitions, proofs and machine design choices at each step.

## One, compatibility and resolution

For moduli `m_i >= 2`, define `rho(x) = (x mod m_i)_i` and `e = rho(1)`. The additive orbit of e has period `L = lcm(m_i)`. It equals the compatible tuples satisfying `r_i = r_j mod gcd(m_i,m_j)`. This is the generalized CRT description of the scalar-compatible state.

For pairwise coprime moduli the compatible state equals the full product. With overlapping moduli, the raw product is larger and the scalar-compatible subspace must be distinguished. Example: views modulo 6, 10 and 15 resolve a scalar modulo 30, not modulo 900.

## Exact observation

Let `h : S -> O` be the available observation and `f : S -> T` the requested output. A function `g : im(h) -> T`, defined on observations that actually occur, satisfying `f = g o h` on the admissible states exists exactly when

```text
h(x) = h(y)  implies  f(x) = f(y).
```

This specifies which questions an observation can answer, including when the admitted source domain is empty. It does not require a total answer on arbitrary unobserved elements of O. Constructing an efficient g, producing authentic observations and maintaining admissibility are additional implementation obligations. The Lean theorem `ExactObservation.recoverable_iff` uses precisely this observation-image domain. The package also contains explicit ring/integer constructors; there is no uniform computational cost assigned to every abstract instance.

## Adjacent-anchor example

For `M=36`, `A=37`, `X=1000`, the observed residues are `r=28` and `s=1`. The positive query yields `(28-1) mod 37 = 27`, which is `floor(1000/36)`. The negative query yields 10, the residue of -27 modulo 37.

For `X=2332`, the two readings are again 28 and 1, while the quotient is 64. The query still correctly yields `64 mod 37 = 27`. A known admissible quotient window distinguishes the intended integer. The universal congruence and exact representative selection are separate results.

## Contribution record

Evaluate the program through six questions: what state is carried; how observations are produced and bound; which outputs are determined; which operators preserve semantics; what arithmetic and bit-complexity costs are counted; and what independent implementation evidence demonstrates the claimed benefit.

Prior-art comparison is an ongoing research task. This seed establishes a source-backed position, not an exhaustive priority review.
