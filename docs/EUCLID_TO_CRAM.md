# Euclid's text, its consequences, and CRAM

**Theory of the One develops the consequences of Euclid's account of unity, number, and measurement for exact computation. CRAM is the machine architecture developed from that foundation.**

The research begins by reading the source statements as written. Quotations keep their edition and wording. Modern notation makes definitions and deductions explicit. Every derived result names its premises, so a reader can inspect each step from the source to the computation.

## Four layers of the work

| Layer | Material | Verification question |
|---|---|---|
| Euclid's text | Edition-identified statements on unity, number, measurement, divisibility and proportion | Is this the text actually supplied by the named edition? |
| Theory of the One | Definitions, derivations and proofs of consequences for exact computation | Does each conclusion follow from its stated premises? |
| CRAM | State representations, observations, typed operators and execution contracts | Does this implementation preserve the proved meaning? |
| Applications | Concrete use in encryption, signals, numerical methods and other systems | Does the application satisfy the arithmetic and domain-specific conditions? |

## A concrete chain

1. **Unity and multitude.** Book VII Definitions 1–2 establish the counting unit and number as a multitude of units. The thesis preserves the supplied English wording in Appendix A and identifies the Greek edition in Appendix B.
2. **Measurement.** The definitions of part and multiple concern exact measurement. Propositions 1–2 use repeated subtraction and remaining quantities to establish common-measure results.
3. **Explicit arithmetic formulation.** For positive integers x and m, successive measurement gives `x = q*m + r` with `0 <= r < m`. The modern quotient/remainder formulation states the operation and its domain. Zero and signed integers are introduced explicitly when extending that domain.
4. **Coordinated observations.** Define `rho_B(x) = (x mod m_i)_i` and `e_B = rho_B(1)`. Repeated addition shows `rho_B(n) = n*e_B` for nonnegative n; additive inverses extend the identity to signed integers. The period is exactly `lcm(m_i)`, since a multiple of e_B vanishes precisely when every m_i divides it. The thesis proves compatibility and identifies the relation to generalized CRT.
5. **Derived queries.** With authentic readings `r = X mod M` and `s = X mod (M+1)`, write `X = r + M*K`. Reducing modulo `M+1` gives `s = r-K mod (M+1)`, hence `(r-s) mod (M+1) = K mod (M+1)`. An explicit admissible window selects the exact integer quotient when needed. These are the positive StarLift query and its representative-selection condition.
6. **Machine realization.** CRAM retains coordinated residue/anchor evidence and computes the required query on demand. Source/phase binding, lane scheduling, configuration and serialization are machine contracts supporting that realization.

The chain makes the mathematical connection inspectable. It preserves Euclid's words while identifying the modern definitions, proved extensions and engineering choices needed to carry the computation through.

## Reading path

Start with the [manuscript's Book VII chapter and appendices](../foundations/theory_of_the_one/theory_of_the_one.md), continue to [the foundations](FOUNDATIONS.md), then [the machine contract](ARCHITECTURE.md). The [Lean package](../formal/universal/README.md) records formal scope; [evidence status](../evidence/STATUS.md) distinguishes fresh execution from supplied compiler receipts.

## Source editions

- [Euclid, Elements, Book VII, Heath edition via Perseus](https://www.perseus.tufts.edu/hopper/text?doc=Euc.+7&fromdoc=Perseus%3Atext%3A1999.01.0086).
- The manuscript's Greek appendix identifies Heiberg's text as reproduced in Fitzpatrick's corrected 2008 edition. Its English appendix retains the author's supplied rendering. These edition distinctions remain explicit.
