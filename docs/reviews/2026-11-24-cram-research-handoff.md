# CRAM mock theta research handoff

The program asks when degree-labeled Safe Basis readings determine a continuous observable to a requested precision, and which properties of that observable distinguish the mock-theta or crank construction. **Start with the finite integral at order 34.** Lean already bounds the missing shadow tail. The next deliverable is a numerical enclosure with its own proved error, which can then be combined with the tail bound.

## What is ready to use

| Result at the proof baseline | Where to start |
| --- | --- |
| All 17 named functions have finite coefficients and packet evaluations. For third-order $f$, Lean differentiates the infinite completion and identifies the five zero mod-11 shadow sectors. | [Proof map](../../.agents/skills/cram-mock-theta-bridge/references/proof-map.md) |
| For authentic readings, order-10 packets stabilized at five terms and a same-source mod-17 lane determine the translated order-34 estimate. Its error against an order-34 endpoint stabilized at 17 terms is at most $7680/\lfloor\sqrt{24D+1}\rfloor$. At $D=4267$ the bound is 24 and the measured error is about 0.369820. | [Theorem and replay](2026-11-22-cram-shadow-period.md#a-certified-cutoff-for-the-translated-endpoint) |
| The integer Watson congruence holds for every positive half-order. Root multiplicity at $-1$ over prime fields is classified for $p>3$. The order-24 starting cusp already has an exact averaged endpoint. | [Watson congruence](2026-11-22-cram-even-roots.md) · [Order-24 endpoint](2026-11-22-cram-shadow-endpoint.md) |

The analytic baseline at `e7cf1b8` contains 1,783 theorem declarations among 2,074 declarations in 67 modules. Its receipt pins Lean, Mathlib, the local core and analytic sources. The finite order control below has its own replay. [Baseline commit](https://github.com/Skyelabz210/Theory-of-the-One/commit/e7cf1b8f34726c49f2c1f0733748b90f6f3b8ce1) · [Analytic audit](../../adapters/MockThetaAnalytic/verification.json)

## Results that change what to try next

- **Family order.** For primary 30030 and target 34, every named series has a nonzero coefficient on both parity orbits. Lean proves the least positive winding resolution is 17 in every signed chart for every one of the 17 functions. More generally, at one shared target and chart, the minimum for a whole degree packet is either 1 or the reduced target period. This rules out the proposed common-resolution definition of historical order. [Lean control](../../formal/controls/OrderTest.lean) · [Axiom replay](../../evidence/current/profinite-mock-theta/order-test.log)
- **Hecke action and cohomology.** At size three, the fixed crank mask gives 0 at degree 1 where the opposite ordering of the $T(25)$ calculation gives $-24$. The joint crank coordinates have an explicit transported action. For cohomology, a closed finite winding cocycle has $\delta^1 w=0$, while the full analytic shadow is nonzero. A proposed map must specify its domain, coefficients and action. The FKTY period defect is a candidate for a separate composition law. [Hecke calculation](2026-11-21-cram-shadow-reconstruction.md#the-hecke-square-at-five) · [Analytic shadow](../../adapters/MockThetaAnalytic/MockCompletion.lean)
- **Fluid discrimination.** The companion experiments report zero native net winding for mass-conserving Burgers. A lifted gradient at the first inviscid shock grows under spatial refinement, while the matched positive-viscosity Burgers gradient stays bounded. The smooth NS shear also stays bounded. A finite-time static energy bound or a bound that applies to every path cannot distinguish these equations. Preserve the observable, viscosity, signed lift and quantifiers when comparing runs. [Native NS observable](https://github.com/Skyelabz210/NS-3D-solver_n32-ntt6/blob/83887a22e8c5aedbb2aad32172cf4bffdc3e62c2/arena/crates/ns_winding_v2/src/lib.rs)
- **Filter identification.** The calibrated shear experiment identified size two among 64 Boolean masks with one mod-11 winding digit. Size nine shares that digit. A second base-11 digit separates this pair. A new claim of crank specificity needs held-out data and the named alias. Generic bounded masks also obey the heat transport identity. [Partition definitions](../../formal/universal/PartitionCrank11.lean)

The fluid findings above come from companion packets. Their source trees and numerical receipts are separate from this repository’s analytic audit. For a handover between workspaces, identify each packet by the SHA-256 of its `SHA256SUMS` file and check its contents with `sha256sum -c SHA256SUMS` from the unpacked directory.

| Companion packet | SHA-256 of manifest |
| --- | --- |
| `cram-falsification` | `d52d96fe4bdbd94ec109d2c6f9dd3a16cc989e56e2ec1772ceab105c162650e9` |
| `cram-shear-bound` | `dae938031d832bbbac1a1b1be7a0b0b2a4fa4e44d94024f294770e336bdb4431` |
| `cram-filter-identification` | `c34aa73bebda39628d020af4397688c61c9aaecaaa1e8a7d561b019d1fd2c373` |

## Reproduce the starting point

Use the pinned Lean/Lake toolchain and `mpmath==1.3.0`. Run from the repository root in Bash. The first command compares the endpoint replay to its recorded result. The second group rebuilds the finite dependencies and checks every printed axiom list against the standalone order-control receipt.

```bash
set -eo pipefail
python3 adapters/MockThetaAnalytic/check_shadow_period.py | diff -u evidence/current/quantum-radial/shadow-period.json -
(
  cd formal/universal
  lake --wfail build MockThetaPhi MockThetaPsi MockThetaChi MockThetaFifthZero MockThetaFifthOne MockThetaSeventh
  lake env lean -DwarningAsError=true ../controls/OrderTest.lean | diff -u ../../evidence/current/profinite-mock-theta/order-test.log -
)
```

For the full clean analytic rebuild, run `(cd adapters/MockThetaAnalytic && python3 verify_analytic.py && cmp .lake/verification/receipt.json verification.json)`. Record the source revision, input hypotheses and a failing control with each new result. [Replay guide](../../.agents/skills/cram-mock-theta-bridge/references/replay.md)

## Order-34 evaluation

### Enclose the finite order-34 integral

Use directed rounding or rational intervals for the finite Gaussian-mode integrals, including the square-root branch on the cusp ray. At degree 4267 produce a complex enclosure and a proved absolute error for the numerical evaluation. Check it against an independently enclosed terminating sum after allowing for the separate truncation error. [Period derivation and numerical replay](2026-11-22-cram-shadow-period.md)

### Certify the total error for a requested tolerance

After the finite integral has an enclosure, budget truncation, arithmetic, order-10 evaluation and phase errors against one positive rational tolerance. Return a center and certified radius. Exercise signed sources −1, 0 and 30030, with a control that omits the mod-17 reading and exposes the phase ambiguity. [Cutoff theorem](../../adapters/MockThetaAnalytic/ShadowPeriod.lean)

### Reduce the coefficient cost of the order-34 bound

Keep the published cutoff as a baseline. Use the exact cusp separation and normalization or a sharper tail estimate. Prove a smaller sufficient degree for a stated tolerance and report the inclusive reading count and the executable cost separately. [Published cutoff and constants](2026-11-22-cram-shadow-period.md#a-certified-cutoff-for-the-translated-endpoint)

## Proof extensions

### Transport the joint Hecke action to a cusp period

Start at T(25) using the six transported crank coordinates. Specify the geometric operator, cusp action, weights and multiplier. Prove one commuting identity with the period correction or give a coefficient or cusp witness where it fails. Keep the size-three fixed-mask calculation as a regression. [Hecke square and conventions](2026-11-21-cram-shadow-reconstruction.md#the-hecke-square-at-five)

### Test composition of the FKTY period law

Specify the subgroup, slash action, multiplier branch and coefficient space. Starting from the order-34 to order-10 identity, derive and test the defect for two composable transformations. A global cocycle claim requires the composition law on its whole stated domain. [Order-34 transport](../../adapters/MockThetaAnalytic/Order34QuantumPackets.lean)

### Formalize the modular transformation for the completed f vector

Match the component, level and normalization to Zwegers. State the generators, multiplier, harmonicity and cusp-growth obligations separately. Deliver the checked vector transformation for the chosen generators and identify which remaining Maass-form hypotheses have proofs. [Completion and cited transformation](2026-11-20-third-order-analytic-shadow.md)

### Construct the fifth-order chi-zero completion

Start from the verified disk series for χ₀. Pin the published normalization and companion components, define the nonholomorphic correction, and prove its shadow identity in Lean on the upper half-plane. Include an independent coefficient or sign check. [Fifth- and seventh-order disk series](../../adapters/MockThetaAnalytic/FifthSeventhHolomorphic.lean)

### Construct the seventh-order F-zero completion

Start from the verified disk series for seventh-order ℱ₀. Identify the published vector and unary theta shadow, justify differentiation of the infinite correction, and check the normalization against independent coefficients. [Seventh-order coefficients](2026-11-20-seventh-order-mock-theta.md)

### Classify the exceptional Watson characteristics

Compute Taylor coefficients at −1 in characteristics 2 and 3 for the cleared Watson polynomial. Retain the k=5 characteristic-3 witness and handle identically zero reductions explicitly. Deliver a proved classification on a stated range or an exact counterexample to a proposed formula. [Current multiplicity theorem and controls](2026-11-22-cram-even-roots.md)

### Characterize Watson lifts modulo powers of eleven

Test divisibility by powers of X+1 over ℤ/11ᵃℤ using exact monic division. Retain k=11, 21 and 241 as controls and distinguish a zero value from higher divisibility. Prove a criterion with explicit ranges in a and k, or record its first obstruction. [Prime-power examples](2026-11-22-cram-even-roots.md)

## Fluid comparison

### Reproduce the common Burgers and Navier-Stokes observable

Pin the two solvers and the measurement before running either. Fix the physical gradient, observation point, time horizon, viscosity, floor scale, mesh and signed lift. Reproduce the inviscid shock, matched-viscosity Burgers and smooth shear controls. Report mesh and time refinement separately and preserve distances to digit thresholds. [Pinned NS tracker](https://github.com/Skyelabz210/NS-3D-solver_n32-ntt6/blob/83887a22e8c5aedbb2aad32172cf4bffdc3e62c2/arena/crates/ns_winding_v2/src/lib.rs)

### Test crank specificity on held-out shear data

Fix a new amplitude or observation schedule before testing it. Compare a named crank against unrelated even masks and the size-two/size-nine alias. Record real enclosures, quantization margins and which same-source digit resolves each collision. A held-out failure is an informative result. [Partition-crank source](../../formal/universal/PartitionCrank11.lean)

### Construct or refute a joint fluid-to-shadow intertwiner

Specify both evolution actions independently and a single map on a declared space of Fourier data. Test its time and Hecke squares for every admitted datum, allowing the proved transport of crank coordinates. Use a generic heat mask and the size-three fixed-mask failure as controls. Deliver a quantified identity or a concrete obstruction. [Joint Hecke action and failed fixed mask](../../adapters/MockThetaAnalytic/ShadowHecke.lean)

### Bound the nonlinear commutator beyond triangular shear

After fixing the common observable, derive its actual nonlinear term on a declared larger velocity class. Track derivative loss, pressure and vortex stretching. Supply a cutoff-independent bound in a stated norm or a sequence violating it. Include a non-crank filter with the same norm as a control. [Pinned NS research revision](https://github.com/Skyelabz210/NS-Regularity/commit/bcc3587be16241295a85beceb7b15f006079169a)

### Pass a fluid winding estimate to the continuum

Use the common observable and a uniform nonlinear bound. Prove convergence of the discretized measurement on a fixed physical horizon, control threshold crossings and distinguish signed integer winding from its mod-11 digit. State the flow class and any further condition required for a horizon-uniform result. [Source and observation contract](../ARCHITECTURE.md)

## Further investigation

### Test an intrinsic candidate for Ramanujan order

Use the fixed-target counterexample as a rejection test. Derive an invariant from a series or its specified representation before consulting family labels. Apply one rule to all 17, report each mismatch, and say which part of Dyson’s group-theoretic question the result addresses. [Order control](../../formal/controls/OrderTest.lean) · [Mock Jacobi structure, §9.5.2](https://arxiv.org/abs/1208.4074)

### Map the historical mock-theta criterion into Lean

Griffin, Ono and Rolen proved that Ramanujan’s examples satisfy his original definition. Trace their hypotheses to the 17 normalized coefficient series and the available cusp results. Deliver a per-function coverage table and one formal implication with the required root-of-unity quantifiers. [Griffin–Ono–Rolen](https://doi.org/10.1073/pnas.1300345110)

### Build the topological completion of the admitted residue system

Define the inverse-limit topology and prove continuity of the cylinders. For a specified cofinal family, identify the Pontryagin dual with the direct limit of its finite character groups, or exhibit an admission obstruction. List the additional summability or measure hypotheses for an infinite transform. [Profinite construction and open obligations](2026-11-20-profinite-mock-theta-formalization.md)

### Test one proposed BPS coefficient identification

Select a published black-hole charge sector and its indexed degeneracy generating function. Specify the Jacobi component, normalization, and extraction rule before comparing exact coefficients. Deliver a sourced identification or a mismatch. A numerical entropy fit alone leaves the identification open. [Dabholkar–Murthy–Zagier](https://arxiv.org/abs/1208.4074)
