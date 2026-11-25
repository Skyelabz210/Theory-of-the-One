---
name: cram-mock-theta-bridge
description: >-
  Trace, reproduce, and extend the Lean bridge from CRAM Safe Basis observations
  to Ramanujan's mock theta packets, crank and analytic shadow modulo 11,
  quantum radial limits, and Watson polynomial congruences. Use for coupled
  anchor admission, finite root evaluations, FKTY cusp transport, prime-power
  root multiplicity, or a proposed discrete-to-continuous theorem using these results.
---

# CRAM Mock Theta Bridge

## Identify the requested result

1. Name the function, input, domain, and output. Record the coefficient ring, truncation, root order, admissible period, and signed-source readings as applicable. For a limit, give the normalization, approach and topology.
2. Locate the current Theory-of-the-One checkout. Read its local instructions, [proof map](references/proof-map.md), and the exact theorem statements. Check the working tree and match the current source to its receipt. Follow the repository's separate Std-only core and Mathlib analytic adapter.
3. Compare the requested result with the strongest theorem you find. State the remaining hypothesis, extension, or integration step. Use `navigate-cram-proofs` for wider coverage searches and `cram-verified-patterns` for CRAM architecture decisions when available.

## Compose observations and packets

Keep the fixed Safe Basis \(\{2,3,5,7,11,13\}\) with primary \(M=30030\). Bind auxiliary readings to the same source, operation, phase and epoch. For the signed chart \(X=r+MK\), derive the required residue of \(K\) on demand. Retain residue and anchor evidence in persistent state.

For positive anchor moduli \(A_i\), let \(A=\operatorname{lcm}_i A_i\). Use quotient resolution \(H=A/\gcd(M,A)\) and source period \(L=MH=\operatorname{lcm}(M,A)\). An empty anchor list supplies \(H=1\). For target order \(b>0\), the universal target-residue query and primitive phase have the exact test \(b/\gcd(M,b)\mid H\). Track overlaps through the LCM. A failed test gives an alias by shifting the source by \(L\).

Pair the complete finite coefficient packets with the root character using `ResidueSeries` and the family theorem. The source lanes supply the admitted phase. The coefficient distribution comes from the named series and cutoff. Where an individual polynomial or observable allows extra cancellations, test its own fibers.

## Choose the proof that reaches the requested layer

- **Families and crank.** Reuse the coefficient and finite root theorems for the four third-order, ten fifth-order, and three seventh-order functions. Give the partition statistic and the weight of each size in a crank calculation. For a paired S8 crank query, provide the stipulated signed increment and both readings.
- **Differential shadow.** Use the normalized infinite completion of third-order \(f\) on the upper half-plane. Under \(\xi_{1/2}\), an input projection in class \(r\) selects shadow class \(-r\). Use degree-labeled S6 coefficient prefixes for the parity reciprocal, signed eta lift and moment reconstruction. Track input lookahead and sector transport when using the Hecke stencil.
- **Radial and quantum values.** For \(f\) at a primitive \(2k\)-th root, use the compensated series \(f(t\zeta)-(-1)^k b(t\zeta)\) as \(t\uparrow1\). Match the interior Taylor series, the packet period, and a diagonal cutoff that dominates the theorem's threshold. For FKTY, use the reflected rational argument and the documented factor. Apply the order-34 to order-10 period identity with the appropriate source readings.
- **Integer congruence.** For the cleared Watson difference \(\Delta_k=W-(D-1)B_k\), reuse \(X^k+1\mid\Delta_k\). For positive even \(k\), each odd \(s\mid k\) gives the additional divisor \(X^s+1\) with quotient value \(2k/s\) at \(-1\). Over \(\mathbb F_p\) for \(p>3\) and \(k>0\), the exact multiplicity at \(-1\) is \(2\) for odd \(k\) with \(p\mid k+1\) and \(p^{v_p(k)}\) otherwise, where \(v_p(k)\) counts the factors of \(p\) in \(k\). Check characteristic, parity, and the exact polynomial before transporting this result.

Use distinct symbols for Ramanujan's family labels, the order of a root, its half-order \(k\), and the coefficient characteristic \(p\). Identify whether a mod-11 claim concerns a source phase, a partition crank, a Fourier projection, or the coefficient ring.

## Extend and verify

1. Start from the closest proven lemma. For a proposed congruence, measure the full monic remainder or first nonzero Taylor coefficient in exact arithmetic. For an observation claim, test exact collisions on the admitted domain. Run a positive instance, a boundary instance and a near-identical failed premise.
2. For a new analytic step, identify the interior series, compensation, bounds, uniformity and required limit interchange. For a proposed transfer to a new evolution, define both actions and the map between them on a common domain. Prove the intertwining identity for every admitted datum. A continuum conclusion requires estimates uniform in the cutoff and a limit theorem for the actual evolution.
3. Use the [replay commands](references/replay.md). For changed proofs, build the affected module, exercise the public theorem through a typed example, and run its source-bound audit. Keep the independent check and the Lean proof traceable to their exact inputs.
4. Deliver the theorem, calculation or counterexample with exact hypotheses, source symbols, revision or working-tree status, and matching evidence. Report reproduced results from actual runs. Keep live counts and receipts in the project records.
