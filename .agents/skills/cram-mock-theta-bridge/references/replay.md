# Reproduce the evidence

Use the current Theory-of-the-One checkout and its pinned Lean/Lake version. Run the following from the repository root in Bash. Select the checks that exercise the requested result.

## Independent replays

```bash
(
  set -e -o pipefail
  python3 tools/check_watson_even_roots.py | diff -u evidence/current/quantum-radial/watson-even-roots.json -
  python3 adapters/MockThetaAnalytic/check_shadow_reconstruction.py | diff -u evidence/current/analytic-shadow/reconstruction.json -
  python3 adapters/MockThetaAnalytic/check_shadow_period.py | diff -u evidence/current/quantum-radial/shadow-period.json -
  python3 adapters/MockThetaAnalytic/check_shadow_endpoint.py | diff -u evidence/current/quantum-radial/shadow-endpoint.json -
)
```

The Watson checker constructs full integer coefficients using denominator suffixes and long division. A first nonzero remainder after \(m\) zero remainders gives multiplicity \(m\) over the chosen field. Use `evidence/current/quantum-radial/README.md` for the order-24 and order-34 radial runs and `evidence/current/analytic-shadow/README.md` for the numerical shadow replay. Report numerical comparisons with their precision and exact replays with the checked cases and source hash.

## Lean checks

From `adapters/MockThetaAnalytic`, build the affected modules and check the public entry points.

```bash
lake --wfail build FOREvenRoot FORWatsonMultiplicity
lake env lean -DwarningAsError=true --stdin <<'LEAN'
import FOREvenRoot
import FORWatsonMultiplicity
open MockThetaAnalytic
#check fPackets_tendsto_boundary_from_coupled_anchors
#check normalized_fPackets_tendsto_fkty
#check watson_even_polynomial_congruence
#check watson_rootMultiplicity_at_neg_one
#eval (List.range' 1 96).all watsonBoundaryCertificate
#eval watsonBoundaryCertificate 1001
LEAN
```

Apply the theorem to an explicit typed example in the relevant module or `AnalyticAudit.lean`. For a clean analytic rebuild, run `(cd adapters/MockThetaAnalytic && python3 verify_analytic.py)` from the root. It writes a candidate receipt and logs under `.lake/verification/`. Match its source and lock hashes and inspect the axiom audit before refreshing the project receipt. The finite suite is `python3 tools/verify_profinite_mock_theta.py --lean lean` and refreshes the core and finite receipts. Run it in a checkout where those updates belong.

## Worked checks

- **A new anchor for order 24.** From \(M=30030\), compute \(24/\gcd(M,24)=4\). Compare same-source mod-4 and mod-8 anchors. The former supplies \(H=2\) and aliases the phase after a shift by \(60060\). The latter supplies \(H=4\), giving period \(120120\). Reuse `Order24Source.anchor_resolutions` before deriving a new observation theorem.
- **A repeated Watson factor.** At \(p=11,k=21\), the first two Taylor coefficients at \(-1\) vanish and the quadratic coefficient is 3. At \(p=11,k=22\), \(X^{11}+1\) is the even-period divisor and its quotient at \(-1\) is 4. Test both by exact division. To probe the prime restriction, check \(p=3,k=5\), where the first nonzero remainder follows three zero remainders. To probe coefficient-ring lifting, the audit checks the simple root for \(k=21\) modulo 121 and the double root for \(k=241\) modulo 121.
- **A proposed shadow extension.** Determine whether the claim is a crank character, a full \(\xi_{1/2}\) identity, or an endpoint period. Check the relevant declaration with its inputs. Test parity omission or aggregation by residue bin before discarding degree labels. In the reconstruction replay, the Hecke stencil at output \(q^1\) gives \(-24\) with the full input. Zero-padding the missing \(q^{25}\) coefficient gives \(-4\). A fixed size-three mask at the output degree gives zero, while the transported crank reading gives \(-24\) in that component.
