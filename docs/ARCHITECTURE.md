# Current machine contract

CRAM is the machine architecture developed from Theory of the One. The foundation starts with Euclid's definitions and develops explicit consequences for exact computation. This contract specifies the representation and execution choices that realize the results. See [the foundational chain](EUCLID_TO_CRAM.md).

## Persistent state

Retain residue readings and authentic anchor/phase evidence, configuration identity, operation/source/epoch bindings, and public admissibility information. Derive winding or magnitude only when an operation requests it. A mathematical proof variable X or K is not a runtime storage requirement.

Public bounds must not conceal a scalar secret value. Changing coordinates requires a declared transition preserving authentic evidence; it is not permission to synthesize a new independent observation from insufficient information.

## Configuration

A machine configuration declares:

1. Logical basis and physical packing, including S6 `{2,3,5,7,11,13}` or an explicitly named alternative.
2. Independent carriers and dependent views, with the scalar resolution proved from their LCM.
3. State type: scalar-compatible observations or a heterogeneous product state.
4. Operators and permitted lane-level heterogeneity, synchronization and phase relations.
5. Required input evidence and each output's mathematical meaning.
6. Signed/range admission, refinement and recovery obligations.
7. Observation boundaries and allowed serialization fields.

S6 is a profile with period 30030, not automatically a ciphertext modulus or a security parameter. The historical S8 extension is a separately named profile. Logical lane roles survive composite packing.

## Query and operation boundaries

For general coprime `M,A`, the positive quotient residue is `((s-r) * inverse(M,A)) mod A`. At adjacency it is `(r-s) mod (M+1)`. Nonunit anchors require their own reduced-resolution contract. The paired-reading query does not take scalar X or K as an input.

State explicitly whether an operation is modular reciprocal, exact integer division, quotient/remainder, coefficient rescaling, FPD, or encrypted word-circuit division. Each has distinct prerequisites and consumers.

No Garner/mixed-radix synthetic emission belongs in the residue compute path. A declared boundary value observation or external exact test oracle has a separate contract. Preserve heterogeneous lane execution; do not substitute a serial scalar reconstruction pipeline.

## Reversibility and execution

Prove reversibility for the actual operator and admitted state space, including retained remainder or inverse witnesses when required. Safe-basis membership alone is not an invertibility theorem. Logical invertibility, probabilistic detailed balance, lane-order confluence and physical energy expenditure are separate properties.

## Acceptance sequence

Map a candidate implementation's ingress, state, producers, dispatch, query, consumer and egress. Verify arithmetic contracts and source binding; exercise rejection and alias controls; then benchmark the real path. Apply cryptographic or scientific validation to the corresponding application after its functional connection is established.

This seed imports foundational source. It does not declare a production CRAM runtime or migrate the NINE65 engine.

## Verified core and integration boundary — 16 November 2026

The concrete Lean `ResiduePrimitives.State` stores exactly `main` and `anchor`. Its public `Frame` supplies the moduli and an inverse certificate. `kQuery` derives the quotient residue on demand; comparison uses that result and the main remainder. Bounded division and GCD keep their arithmetic operands and results as paired residue states. The fresh compiler and executable receipts are in `../evidence/current/lean/`.

This core's correctness theorems admit natural inputs in `[0, M*A)` and, for division, a positive divisor in that same window. Divisors may share factors with either observer modulus. The frame itself requires an inverse of M modulo A; a nonunit anchor has separate query theorems and is not a concrete `Frame` instance without that certificate. Signed query identities do not change the concrete natural-number divmod API.

The raw two-field `State` does not enforce frame identity, source/operation/epoch binding, normalization or admission on external inputs. An integration wrapper must establish those conditions before invoking the core. The theorem premises describe valid states; they are not runtime rejection checks.

The included divmod algorithm is a proved repeated-subtraction reference with public fuel. The fixed subtraction/multiplication count in `CostedReadout` describes a quotient readout expression. An optimized division implementation, adjacent-query specialization, scheduling model and performance claim each require a concrete connection to that expression and the admitted-state contract.
