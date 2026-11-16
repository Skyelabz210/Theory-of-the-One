# Independent formal-semantics audit

**Review record:** findings refer to the pinned pre-repair source. See [the integrated analysis](2026-11-16-deep-analysis.md) for the completed repairs and fresh execution receipts. Source line references remain pinned to that original commit.

Source: `Skyelabz210/Theory-of-the-One`, commit `f66b9a74eecf76ce5b4ecc978879b60d17f71df7`. Static audit completed 2026-11-16. Paths below are relative to the repository; `U/` abbreviates `formal/universal/`. All twelve Lean files, `check_proofs.py`, the Lake configuration, current architecture contract, and all fourteen numbered manuscript theorem statements were read. Applicable repository instructions and architecture references were also read.

This worker did not install or compile Lean. The coordinating worker reports a fresh successful pinned Lean 4.27.0-rc1 audit of 130 declarations, with 30 having no axiom dependencies and the remaining dependencies limited to `propext`, `Classical.choice`, and `Quot.sound`. Its raw execution evidence is authoritative for that result. The imported historical receipt was read only as historical evidence. Smoke execution is separate from the proof-audit command.

## Overall conclusion

The package has a substantial, coherent formal core. It proves exact observation/fiber criteria, affine phase subtraction, sided ring readouts, signed integer congruence and interval recovery, shared-factor reduction, combined-anchor LCM resolution, direct target transport, and a concrete bounded natural-number comparator/division/GCD implementation. It does not merely assume the concrete comparator or divisor implementation correct: `ResiduePrimitives.ops_correct` discharges those obligations from actual paired-residue code.

No current theorem was found to conclude only `True`, introduce a custom arithmetic axiom, exploit an inconsistent universal premise, or replace its intended result with a trivial existential. Abstract correctness assumptions are explicit, and the important concrete instances discharge them. Empty admitted sets can make some generic specification theorems vacuous, as expected; positive-capacity concrete frames and their nonempty admitted domains prevent that from explaining away the executable result.

The package is not a formalization of all fourteen manuscript theorems, a production provenance protocol, a signed division implementation, an encrypted implementation, or an end-to-end performance result. Those are exact limits of the statements and executable paths, not evidence against the proved identities.

## Findings and precise repairs

### F1 — Strong formal core, incomplete manuscript coverage

The number 130 counts declarations, including supporting algebra, wrappers, correctness lemmas, and operation counts. The manuscript coverage must be assessed claim by claim. The manuscript coverage table below is the needed publication bridge. In particular, no formal carry cocycle, generalized-CRT existence/compatibility theorem, heterogeneous operator semantics, value-quotient ring construction, finite-group order obstruction, or profinite completion construction is present.

Repair: publish a claim-to-symbol ledger alongside the manuscript; retain written-proof status for missing claims. Formalize the missing named propositions in dependency order rather than changing correct existing theorems to match stronger labels.

### F2 — Source and admission are proved premises, not validated ingress

`U/ResiduePrimitives.lean:16` defines raw `State` with two `Int` fields, `main` and `anchor`. It contains no frame identifier, source identity, operation, phase, epoch, canonicality certificate, or range certificate. `Frame.less` at line 38 and `Frame.divmod` at line 162 accept arbitrary raw states. Their correctness theorems apply to `f.encode n` for admitted `n < f.capacity`.

This is an appropriate small arithmetic model and is explicitly not the production engine. Its paired update proofs do ensure that increment and admissible subtraction preserve the same mathematical source operation when inputs start authentic. The model does not establish how an external producer makes that premise true.

Concrete mismatch at the boundary: in the 36/37 frame, `encode 1333 = encode 1`; comparing that state with `encode 2` returns true. That is correct for the admitted representative 1 and wrong if a caller silently means 1333. `U/ClosureSmoke.lean:45` deliberately exercises this alias. No runtime predicate on the identical two readings alone can distinguish those intended sources. Similarly, a main reading from one input and anchor reading from another can encode a different perfectly valid bounded integer.

Repair: give production ingress and every producer/consumer transition a checked or proved admission and source-binding contract, including configuration/operation/phase/epoch where the runtime requires them. Do not propose recovering an out-of-window bound or provenance from the same aliased readings. Bind frame identity at the type/API level or validate it externally. Keep those obligations distinct from arithmetic consistency and cryptographic authentication.

### F3 — Three different domains must remain distinct

1. `IntegerSpecialization.query_quotient_congruence` (line 59) covers signed `Int` sources and yields a quotient **residue**, not an unrestricted integer quotient. `query_exact_signed_window` (line 102) selects the integer quotient only under a supplied half-open interval. `StarLift` makes the positive/negative orientation explicit.
2. `ResiduePrimitives.Frame.encode` (line 24), concrete comparator correctness (line 94), and concrete divmod/GCD correctness (lines 171 and 183) operate on `Nat` in `[0,M*A)`. Signed Euclidean division, signed state encoding, and signed overflow/admission updates are not instantiated.
3. Nonunit **observer anchors** are covered by the standalone `nonunitQuery` formula and conditional proofs; the concrete `Frame` at lines 7–13 requires an inverse certificate for `M mod A`, so it does not implement frames with nontrivial `gcd(M,A)`. Nevertheless, its concrete division algorithm does support every admitted positive **divisor** `d`, including divisors sharing factors with either observer modulus. These are different uses of shared factors.

Repair: label API domains explicitly. Add signed algorithms and nonunit-frame constructors only if required, preserving their own admission contracts. Do not describe shared-factor divisors as unsupported, and do not describe the standalone nonunit formula as an integrated nonunit-frame divmod engine.

### F4 — No persistent K or hidden reconstruction in this concrete path

The executable persistent number state is exactly the two residue fields (`State`, lines 16–19). The frame stores public configuration and an inverse certificate, not a per-number lift. `Frame.kQuery` at line 29 derives K on demand; `Frame.less` uses it locally. Division stores the quotient and remainder as paired-residue `State` values, not a scalar winding register. Such a represented quotient is the requested operation result, not an independently carried hidden K for the dividend.

`Frame.divmod` and `Frame.gcd` call the residue loops and primitives; their bodies do not call `Frame.encode`, ordinary semantic `Nat.div`, `Nat.mod`, `Nat.gcd`, or a reconstruction routine. Ordinary numbers in the theorem conclusions and `ClosureSmoke` are specification/test-oracle values. `IntegerSpecialization.targetLaneProjection` (line 263) forms a target residue directly from the target reference reading, quotient reading, and reduced public multiplier; it does not form full `r+M*k` as an intermediate.

The source/readout proofs sometimes use `X`, `r`, `K`, division, or recomposition in their proofs. Those are erased mathematical specification terms, not runtime payload fields. The code therefore supplies positive evidence for no stored K and no Garner/full-source reconstruction in this bounded arithmetic path. It does not establish the same property for an external runtime, serialized records, encrypted bridge, or construction of the aggregate main reading from many payload lanes.

Repair: preserve this implementation shape. Extend the conformance trace to actual ingress, storage, serialization, backend dispatch, and egress before making an integrated architecture claim. Public status of `lo`, inverse, and capacity is an intended interface property, not a formal information-flow property in these types; ensure a purported public window does not encode the secret value.

### F5 — The cost proof is exact but narrow

`U/CostedReadout.lean:47` defines an expression tree with one subtraction and one multiplication; `program_counts` at line 50 proves those two constructor counts. Modular reductions are inside the chosen modular gates (lines 67–73). Input production, inverse setup, memory, normalization bit costs, arbitrary-width operand costs, comparison, exact nonunit factor division, and encrypted execution are outside this count.

`adjacentProgram` at line 76 has one subtraction and zero multiplications and is proved equivalent to the adjacent query. The concrete `Frame.kQuery` still calls the general `IntegerSpecialization.query`; the primitive code does not replace that body with `adjacentProgram`. The semantic equality theorem at `ResiduePrimitives.lean:138` is not by itself a compiler optimization certificate or benchmark. `Frame.less` also has repeated syntactic calls to `kQuery`; no sharing/cost theorem is supplied.

The concrete division is repeated subtraction (`ResidueAlgorithms.divLoop`, line 52), with public capacity fuel. For admitted division by 1 it performs a number of subtract/increment iterations equal to the dividend. This is a valid executable existence/correctness construction, not a constant-cost division result. GCD invokes that division repeatedly. Only the tiny readout expression has the two-gate theorem.

Repair: retain the exact arithmetic-gate wording. If claiming the one-subtraction implementation or efficient division, wire the intended specialized body and prove the relevant program/cost correspondence; measure the whole path under declared widths, hardware, setup, and encrypted/plaintext mode.

### F6 — Proof runner does not include the executable smoke, and stale receipts can survive failure

`U/check_proofs.py:18–21` explicitly lists eleven modules and omits `ClosureSmoke.lean`. The Lake roots/default target also omit it. Thus neither the 130-declaration audit nor an ordinary `lake build` includes its executable checks. This is not a hidden admitted proof: it is an uninvoked separate test.

`ClosureSmoke` checks 36 pairs in frame 2/3, 1,764 pairs in frame 6/7, and nine 36/37 fixtures: 1,809 comparison/divmod/GCD input pairs, each with three assertions. It adds four explicit negative/refusal controls, for 5,431 assertion calls if completed. Its out-of-window control demonstrates aliasing; it does not test an out-of-window rejection mechanism. Line 56 has `#eval main`, so elaborating the module executes the tests; running the same file with a command that also invokes its `main` may execute it twice. Count distinct fixtures separately from repeated invocations.

The audit writes `verification.json` only on success (line 115), but does not invalidate an older successful file at start/failure. An old PASS can therefore remain beside a new failed/partial log. It also hashes the substantive source modules but not the checker itself, `ClosureSmoke`, or `lean-toolchain`; the receipt has a toolchain string but no run timestamp/source commit. The coordinating run should supply those missing provenance fields externally.

The static policy check counts declared and queried theorems, but does not match declaration identities to their corresponding fully qualified `#print axioms` names (lines 78–93). A future file could preserve the count while querying an imported theorem instead of a newly declared theorem. Inspection found no such mismatch in the current 130 declarations. The compiler then checks actual queried transitive axioms, making this a future checker-hardening issue, not a current false receipt.

Repair: add a separate smoke gate and source hash; write receipts to a run-specific directory, or atomically replace a status record with RUNNING/FAIL/PASS and distinguish last success. Include checker/config/toolchain binary/source hashes, time, command and exit status. Match declaration identities to axiom queries or query all declarations from the elaborated environment. Preserve the existing fresh temporary build and foundational-axiom checks.

### F7 — Nonunit edge cases are sound under their certificates

`IntegerSpecialization.nonunit_chart_query` (line 201) assumes `d != 0`, `d | M`, `d | A`, a consistent source/chart decomposition, and an inverse for `M/d` modulo `A/d`. It proves divisibility of the raw observed difference and the quotient residue. It does not assume the desired query equation. Negative observed differences are harmless because exact divisibility is proved before Euclidean division is used. For example, `M=6,A=10,d=2,u=2,r=5,X=11,s=1` gives defect `-4`, quotient `-2`, and resulting class `1 mod 5`, matching K=1.

The formal theorem need not assume `d=gcd(M,A)` because its divisibility and reduced-inverse certificates state precisely what it uses. The positive finite-capacity interpretation is supplied separately by the coupled-anchor GCD/LCM theorem. When `A/d=1`, the output is always zero and contributes no distinction; a width-one interval can select a unique K only because the interval already selects it. This is not new capacity. Negative or zero modulus conventions in unrestricted `Int` identities are Lean's totalized arithmetic, not evidence for a physical finite observer at modulus zero. The positive concrete frame and positive-anchor capacity theorems exclude those cases where needed.

No standalone runtime wrapper verifies the nonunit hypotheses or returns refusal on inconsistent readings, and no executable general inverse setup is provided. `Frame.adjacent` is a constructive exception: it provides inverse `-1` with an algebraic proof, without a GCD search.

Repair: if integrating the standalone nonunit route, construct/validate public parameters and handle malformed readings explicitly. Preserve exact signed division of the defect. Test H=1, inconsistent defects, negative differences, alias windows, and source mismatch separately.

## Manuscript-to-formal coverage

Here “exact core” means an actual theorem states the central result, sometimes in an equivalent stronger general form. “Partial” means components or a restricted instance are present; the complete numbered statement is not machine-checked as written. “Not formalized” does not dispute the written proof. Manuscript path: `foundations/theory_of_the_one/theory_of_the_one.md`.

| Manuscript theorem | Coverage | Actual formal support and remaining gap |
|---|---|---|
| 1, orbit of the One (line 152) | Partial | `CoupledAnchors.source_readings_iff` (192), `main_and_anchor_readings_iff` (203), LCM/kernel/minimal-period results prove the exact residue equality kernel. No explicit diagonal orbit, compatibility-to-existence generalized CRT, image ring isomorphism, cardinality, or raw-product iff pairwise coprime theorem. |
| 2, determined observations (183) | Exact general core; partial complete prose | `ExactObservation.recoverable_iff` (29) proves the general image/fiber factorization iff for arbitrary types. `CoupledAnchors.target_period_iff` (139), specialized to scale 1, proves the residue-target divisibility criterion. The periodic-by-L reformulation, universal divisibility predicate, and bounded equality corollary are not packaged as named formal statements. Factorization is over the observation image, not arbitrary unattainable outputs. |
| 3, anchor-observed winding (213) | Partial, with substantial concrete coverage | `IntegerSpecialization.query_quotient_congruence` (59), `nonunit_query_of_decomposition` (186), `nonunit_chart_query` (201), signed-window results (102,214), star inverse (112), adjacent readout (132), plus `CoupledAnchors.int_reduced_kernel` (41). These prove the formulas and exact width-H recovery under supplied inverse/certificates. No construction of inverse from gcd, complete iff existence of an integer witness for arbitrary raw pairs, or shorter-N-window candidate rejection API/theorem. |
| 4, target winding resolution (273) | Exact central criterion/formula | `CoupledAnchors.target_period_iff` (139) gives necessary and sufficient `b | M*R`; `nat_reduced_kernel` (34) gives the equivalent `b/gcd(M,b) | R`. `IntegerSpecialization.target_projection_of_period_dvd` (238) and chart/target transport (274,287) implement the sufficient direct formula. No integrated dynamic producer of every requested target/base reading is inferred. |
| 5, carry cocycle (300) | Not formalized | No formal carry definition/cocycle, product winding, or signed borrow identity. Additive homomorphism and increment lemmas do not establish those named carry results. |
| 6, order/sign (341) | Partial | `ResiduePrimitives.euclidean_lex_order` (70) proves signed-Int lexicographic order for M>0; `less_encode` (94) realizes comparison for bounded Nat states. `isZero_encode` (117) proves bounded-Nat zero test. Full signed-state comparator, `x<0 iff K<0`, and signed zero criterion are not supplied as the numbered bundle. |
| 7, coefficient witness quotient (386) | Partial | Nonunit defect division supplies the core reduction mechanism; instantiate source multiplier d, anchor d*m, common factor d and inverse 1 to get the quotient class. No direct named theorem proving the unmodded `(t-rho)/d` is in `[0,m)` and equals `q mod m`, including signed dividends. Concrete bounded divmod is a different route, not this witness theorem. |
| 8, exact quotient information (406) | Partial | Reduced kernel (`CoupledAnchors.int_reduced_kernel`) and general query factorization (`ExactObservation.recoverable_iff`) provide the ingredients for `m | N/gcd(N,d)`. No end-to-end named quotient-target iff or valuation-matched prime-power result is present. |
| 9, heterogeneous operators (463) | Not formalized | No family of lane-specific operators or compatible/raw product semantics. Generic `X`/state types can host such a model but do not instantiate one. |
| 10, reversibility (477) | Not formalized as stated | Concrete bounded divmod/GCD correctness retains represented remainder; no proof of the three claimed bijections: modular multiplication iff unit, retained-input update, or signed quotient/remainder bijection. Transduction round-trip on encoded states is a different theorem. |
| 11, value quotient (502) | Not formalized | No admitted-record equivalence quotient, bijection onto semantic image, descended operations, or integer-ring isomorphism. Observation-image subtypes are not this value quotient construction. |
| 12, direction/reversal (575) | Not formalized | StarLift negation of quotient residues is not the conjugation-of-successor theorem or finite translation-invariant-order impossibility. |
| 13, completion (595) | Not formalized | No inverse limit, topology, injective/dense integer embedding, noninteger compatible family, or idempotent construction. Finite coupled anchors cannot substitute for these results. |
| 14, compositional exactness (622) | Partial; exact homogeneous finite-program core | `ExactObservation.refines_composition` (73), `finite_program_exact` (87), and `finite_program_identifies_result` (105) prove total unary transitions on one semantic/state type, with an injective encoding required to identify values. Transfer composition/round-trip (117,126) cover fixed source maps. Manuscript's mixed input/output types, multiple operands, partial admission graphs, and invariant-preserving general loops are not formalized generically; concrete divmod/GCD discharge their own narrower invariants. |

The manuscript's earlier inspection language at lines 660 and 696 is now stale relative to this imported universal package: it describes signed/shared-factor/minimal-target statements as written extensions beyond an inspected bounded theorem. Some are now covered by stronger formal source, but several complete manuscript statements still remain only partially covered. Refresh that status using this ledger and the coordinating worker's fresh execution record; do not erase the original historical scope.

## Module-by-module coverage ledger

### `ExactObservation.lean` — 9 declarations

Runtime/specification distinction is explicit at lines 4–8. `Observed observe` (15) is the image subtype, and `reading` (18) is the authenticated mathematical encoding of a value, not a provenance protocol.

| Symbol / line | Exact hypotheses and supported conclusion |
|---|---|
| `recoverable_iff`, 29 | Arbitrary types and maps. An answer on **observed image values** exists iff query is constant on observation fibers. Reverse direction uses `Classical.choose`; no efficient decoder is constructed. Correct even for empty types/image. |
| `refined_observation_suffices`, 45 | Given `forget(finer x)=observe x` and fiber constancy of old query, finer observations determine the query. Does not construct finer readings. |
| `collision_obstructs_query`, 55 | Two equal observations with unequal wanted values refute fiber constancy for that query only. |
| `refines_identity`, 68 | Identity representation transition refines identity semantic transition. |
| `refines_composition`, 73 | Two supplied refinement equations compose on one type. |
| `finite_program_exact`, 87 | Every total primitive refines its semantic primitive; induction proves equal encoded outputs after a finite list. No injectivity or primitive implementation is silently assumed. |
| `finite_program_identifies_result`, 105 | Adds encoding injectivity and an observed encoded result to infer equality of semantic result. Prevents a constant encoding from supporting stronger identification. |
| `transduction_composes`, 117 | Two supplied exact encoding-transfer equations compose. |
| `transduction_round_trip`, 126 | Forward and reverse encoding equations give record equality on the canonical encoding image; arbitrary historical metadata outside that image is not covered. |

### `UniversalLift.lean` — 15 declarations

Scope is additive **commutative** groups with additive maps. `embed` need not be injective; full recovery requires the explicit separation/readout assumptions. There is no generic theorem that every domain has an efficient inverse.

| Symbols / lines | Exact content |
|---|---|
| `AddMap.map_zero` 29; `map_neg` 34; `map_sub` 39 | Derive zero, negation and subtraction preservation solely from additivity/group laws. |
| `AddMap.same_reading_iff`, 49 | Equality of readings iff their difference lies in the map kernel. |
| `phase_difference`, 65 | From `x=r+embed(k)`, subtracting observed reference yields observed embedded lift. |
| `candidate_iff_kernel`, 76 | A candidate has the same affine observation iff its difference from the source coordinate lies in the composite kernel. Noninjective maps explicitly allowed. |
| `separation_iff`, 87 | Injectivity on admitted coordinates iff no admitted distinct difference lies in the kernel. |
| `lift_query_exists_iff`, 105 | An answer on the admitted observation image exists iff wanted values agree across admitted kernel differences. Existence is nonconstructive. |
| `target_factor_exists_iff`, 125 | On the whole lift group, additive consumer factors through the observation image iff observation kernel is included in consumer kernel. Does not require recovering K. |
| `target_factor_unique`, 146 | Two exact factors agree on all genuinely observed values; no statement on malformed/out-of-image inputs. |
| `target_factor_additive`, 160 | Exact factor preserves induced addition on image readings. It need not extend additively to all of H. |
| `constructive_query_correct`, 175 | A supplied readout correct on admitted composite images gives wanted K-query from source/reference readings. The readout-correctness obligation is explicit. |
| `constructive_lift_correct`, 189 | Specialization with wanted=id gives K under that explicit decoder law. |
| `target_projection`, 202 | Full admitted K readout plus target base reading gives target source value. |
| `direct_target_query`, 217 | Weaker readout of only the target displacement suffices; K need not be emitted. |

`query` (60) takes only a readout and two observations. Its theorem variables X/K do not become runtime inputs. Ring/integer modules supply real instances; abstract `hread` is not evidence of a general decoder algorithm.

### `RingReadout.lean` — 16 declarations

Scope is arbitrary rings, including noncommutative rings; only left-ideal closure requires a commutative source ring. `Observation` assumes/provides additive and multiplicative laws, but not unitality. Inverse certificates are sided equations in the observation ring. These are structure fields and theorem hypotheses, not custom global axioms.

| Symbols / lines | Exact content |
|---|---|
| `Observation.map_zero` 34; `map_sub` 38; `map_neg` 44 | Derived homomorphism laws. |
| `left_mul_sub`, 52 | Standard left distributivity over subtraction. |
| `phase_defect`, 62 | Affine source decomposition gives observed product `h(M)*h(K)`. |
| `unit_readout`, 69 | Left inverse on the left yields observed K for `X=r+M*K`; no commutativity needed. |
| `right_unit_readout`, 78 | Right inverse on the right yields observed K for `X=r+K*M`. |
| `solution_fiber`, 96 | Given one affine solution, all others differ by `LiftNull`: observation of `M*delta` is zero. |
| `injective_on_iff_lift_null_separates`, 107 | Exact injectivity/separation equivalence on admitted lifts. |
| `unit_lift_null_iff`, 125 | Valid left inverse removes multiplier ambiguity, leaving exactly the observation kernel. It does not remove that remaining kernel. |
| `lift_null_zero` 141; `lift_null_add` 146; `lift_null_neg` 152 | Null set is an additive subgroup. |
| `lift_null_mul_right`, 159 | Closure under right multiplication in a noncommutative ring. |
| `lift_null_mul_left`, 166 | Closure under left multiplication with commutative source ring. |
| `target_projection`, 175 | Projecting reduced source decomposition components yields observed X; supplied observed K is required. |

Degenerate rings do not create a false full-recovery conclusion: outputs are always observed K. Concrete effective ring encodings, inverse setup, runtime public/secret distinction, and bit costs remain separate.

### `IntegerSpecialization.lean` — 28 declarations

All functions use exact `Int`. General identities allow totalized zero/negative modulus cases; physical finite-capacity interpretations must use their explicit positive domains. Bounds such as `lo <= k < lo+A` themselves force A positive when inhabited.

| Symbols / lines | Exact content |
|---|---|
| `query_fused`, 23 | Two-reduction query equals fused multiply/reduce expression. |
| `query_of_decomposition`, 30 | Authentic affine decomposition, source anchor reading, and modular inverse imply K modulo A. Base r need not be canonical. |
| `query_chart_of_decomposition`, 49 | Same result with only r modulo A supplied. |
| `query_quotient_congruence`, 59 | Canonical main remainder turns K into Lean's signed Euclidean `X/M`, still modulo A. |
| `query_exact_of_quotient_window`, 70 | `[0,A)` quotient bound converts congruence to exact quotient. |
| `query_exact_of_source_window`, 80 | M>0 and `0<=X<M*A` suffice for that quotient bound. |
| `window_decode_exact`, 93 | Select the unique class representative in `[lo,lo+A)`. |
| `query_exact_signed_window`, 102 | Signed exact quotient after applying the public-window decoder, under its explicit bound. |
| `star_inverse_certificate`, 112 | Inverse -c modulo c*M+1 is proved algebraically; no coprimality search assumed. |
| `star_query_congruence`, 117 | Star anchor readout of quotient class for authentic views. |
| `adjacent_query_subtraction`, 124 | General query at inverse -1 equals reversed modular subtraction. |
| `adjacent_readout_exact`, 132 | Exact quotient in positive source window at M/M+1. |
| `affine_defect_reduction`, 151 | Nonzero common divisor certificates and affine defect equation imply exact divisibility and reduced decomposition. |
| `nonunit_query_of_affine_defect`, 163 | Reduced inverse plus that defect equation proves K modulo A/d. |
| `nonunit_query_of_decomposition`, 186 | Authentic source decomposition derives the required defect equation and divisibility. |
| `nonunit_chart_query`, 201 | Same result with both runtime readings reduced in anchor lane; no wide reference input. |
| `nonunit_chart_query_signed_window`, 214 | Exact signed K if the width-A/d interval contains it. |
| `target_projection_of_decomposition`, 229 | Reduced target components yield X modulo B. |
| `target_projection_of_period_dvd`, 238 | If B divides M*A, using K modulo A leaves target unchanged. |
| `query_target_projection_of_period_dvd`, 251 | Unit query plus period divisibility yields target directly, no K interval needed. |
| `target_lane_projection_eq`, 266 | Lane-only interface agrees with targetProjection given correct reduced base/multiplier. |
| `chart_query_target_lane_transport`, 274 | Authentic chart/source/target-base readings and inverse/period certificates give X modulo B from lane inputs. |
| `nonunit_chart_target_lane_transport`, 287 | Same after common-factor reduction, with B dividing M*(A/d). |
| `query_target_projection`, 301 | Exact nonnegative quotient-window recovery supports arbitrary target modulus. |
| `signed_query_target_projection`, 311 | Same with signed interval selection. |
| `same_views_source_unique`, 324 | Two sources with same paired readings, valid inverse, and same quotient window are equal. |
| `paired_views_periodic`, 341 | M*A is a period for the pair; not claimed minimal with shared factors. |
| `no_unbounded_pair_quotient_decoder`, 348 | For nonzero M,A, 0 and M*A collide but have distinct quotients, forbidding an unrestricted exact quotient decoder from only the pair. |

### `CostedReadout.lean` — 7 declarations

`program_counts` (50) proves one sub/mul AST node each; `program_evaluates_to_readout` (55) identifies its ring interpretation; `program_correct` (60) applies the ring inverse/decomposition proof; `modular_program_evaluates_to_query` (67) identifies normalized modular gates; `adjacent_program_counts` (78) proves one subtraction/zero multiplications for the separate adjacent AST; `adjacent_program_evaluates_to_query` (83) proves equivalence; `ring_is_universal_instance` (103) constructs the additive maps and discharges the abstract decoder condition using ring laws and the supplied sided inverse. Its admitted predicate `True` broadens admission to the whole group; the **conclusion is observed K**, not True.

### `ReferenceChange.lean` — 3 declarations

`shifted_decomposition` (18) changes reference by embed(a) and coordinate to k-a. `shifted_defect` (27) proves the corresponding observed subtraction law. `target_invariant_under_reference_change` (37) requires each old/new domain/readout correctness law and admission of k and k-a; both target expressions then equal the same source target. This does not manufacture a new authentic chart or establish the new interval at runtime.

### `CoupledAnchors.lean` — 19 declarations

The finite list can contain positive repeated, overlapping, composite anchors, or be empty. `anchorLCM []=1`, so empty observations give resolution one, correctly no coordinate distinction. M is Nat and may be zero in algebraic identities; the concrete runtime frame instead requires M>0.

| Symbols / lines | Exact content |
|---|---|
| `anchor_lcm_dvd_iff`, 20 | Finite anchor LCM divides n iff every anchor does. |
| `anchor_lcm_pos`, 26 | Positive anchors imply positive LCM, including empty list. |
| `nat_reduced_kernel`, 34 | A>0: A divides M*v iff A/gcd(M,A) divides v. |
| `int_reduced_kernel`, 41 | Same for signed coordinate differences. |
| `anchor_lcm_int_dvd_iff`, 47 | Signed version of the LCM divisibility criterion. |
| `combined_kernel`, 53 | All observed scaled differences vanish iff reduced LCM resolution divides the difference. |
| `resolution_pos`, 60 | Positive anchors imply positive resolution. |
| `source_period`, 66 | M times resolution equals lcm(M, anchorLCM), without overcounting overlap. |
| `combined_kernel_two`, 72 | Explicit two-anchor form. |
| `combined_kernel_as_lcm_of_resolutions`, 80 | Combined resolution divisibility equals divisibility by LCM of individual reduced resolutions. |
| `resolution_eq_lcm_reduced`, 95 | Equality of those actually computed natural numbers. |
| `same_affine_readings_iff`, 105 | Actual affine source readings agree iff resolution divides k-j. |
| `signed_window_unique`, 120 | Same readings and common width-resolution signed coordinate window imply k=j. |
| `target_period_iff`, 139 | All coordinate differences multiple of R leave target mod b unchanged iff b divides M*R. Necessity uses R versus 0. |
| `combined_target_iff`, 161 | Combined affine anchor information determines target iff b divides the full LCM source period. |
| `resolution_minimal`, 176 | Resolution is an invisible positive coordinate shift and no smaller positive invisible shift exists. |
| `source_readings_iff`, 192 | Equality of any finite list of actual source residues iff LCM divides source difference. This is not arbitrary tuple compatibility/existence. |
| `main_and_anchor_readings_iff`, 203 | Main plus anchors agree iff full M*resolution period divides source difference. |
| `dependent_anchor_resolution`, 211 | Adding an anchor dividing existing anchor LCM changes no resolution. |

This module proves capacity/kernel results, not an executable fusion algorithm or an inverse-limit theorem.

### `ResidueAlgorithms.lean` — 6 declarations

`Ops` (14) supplies capacity and five primitive operations. `Correct` (22) states precisely their required admitted-domain equations. Its use is conditional here and is fully instantiated in the next module.

`encode_injective_on` (34) derives injection from the exact comparison contract; it is not assumed. `divLoop_correct` (80) maintains represented quotient/remainder, requires positive admitted divisor, q+r<capacity and r<=fuel, and proves the returned semantic quotient/remainder pair. `divmod_correct` (107) gives public capacity enough fuel for every admitted positive divisor. `divmod_zero_refused` (120) proves refusal for encoded zero with positive capacity, for any dividend state. `gcdLoop_correct` (127) uses decreasing semantic second operand only in its proof and sufficient public fuel. `gcd_correct` (152) specializes to capacity fuel.

The semantic Nat parameters and proof invariants are not runtime scalar registers. The runtime quotient is represented state; scalar fuel is a public loop resource. The implementation is sequential repeated-subtraction division and Euclidean iteration, not a parallel heterogeneous encrypted circuit or an optimal algorithm.

### `ResiduePrimitives.lean` — 14 declarations

`Frame` has positive M/A and inverse certificate. `State` has only two exact residue observations. `Frame.ops` (144) wires actual functions, and no runtime source reconstruction/semantic oracle call appears in the loops.

`zero_eq_encode` (44) establishes encoded zero. `kQuery_exact` (47) derives bounded natural quotient from the views. `increment_encode` (61) is unconditionally true modulo the frame; semantic admission for later use is separate. `subtract_encode` (65) requires b<=a because Nat subtraction truncates; concrete division proves that premise. `euclidean_lex_order` (70) covers signed Int at positive M. `less_encode` (94) transfers it to bounded Nat states. `encode_injective_on_window` (103) proves faithful bounded encoding. `capacity_positive` (114) excludes empty concrete admission. `isZero_encode` (117) proves the zero test on admitted states. `adjacent_query` (138) proves the simplification. `ops_correct` (154) discharges every abstract primitive law. `divmod_correct` (171), `divmod_zero_refused` (177), and `gcd_correct` (183) instantiate the actual loops, including shared-factor divisors and inexact division.

No general signed Frame encoding, malformed-State refusal, nonunit-observer Frame, phase/epoch protocol, serialization invariant, full-source egress, or encryption layer is included.

### `StarLift.lean` — 13 declarations

The source explicitly says “infinity” is not an arithmetic object in these definitions (lines 6–7). Unbounded integer coordinate inputs can have finite residue outputs without yielding exact unrestricted magnitude.

`negate_residue` (17) and `negative_query_eq_negate` (24) establish residue negation. `negative_query_of_decomposition` (29) gives -K modulo A under authentic decomposition/chart/inverse premises. `positive_adjacent_congruence` (39) gives K modulo M+1; `adjacent_orientations` (47) relates signs; `negative_adjacent_congruence` (54) gives -K modulo M+1; `negative_query_adjacent` (62) proves the adjacent raw-defect simplification. `negative_decode_exact` (70), `negative_adjacent_exact_window` (77), and `positive_adjacent_exact_source_window` (84) turn residues into exact quotients only under their interval/source bounds. `unit_kernel_equal` (92) and `adjacent_kernel_equal` (105) prove precisely equal nullspaces under valid inverse certificates. `negative_nonunit_chart_query` (114) retains common-factor divisibility and reduced resolution for the negative orientation.

No infinity arithmetic, scalar-free arbitrary magnitude recovery, change of finite capacity, or physical time theorem follows from these statements.

### `UniversalKElimination.lean` and `ClosureSmoke.lean`

The umbrella imports the ten substantive modules and declares no theorem. The smoke module imports concrete primitives, checks their actual executable results against independent ordinary Nat oracles at test ingress, and tests four refusal/negative controls. It has no universal theorem declaration and no axiom audit query. Its execution must be recorded separately as described in F6.

## Trust and execution boundaries

The fresh-build runner compiles source modules in dependency order into a new temporary directory, sets `LEAN_PATH` to that directory, verifies the declared pinned version string, fails on compiler errors or warnings, and queries transitive axiom dependencies. That is strong evidence against acceptance based on supplied old `.olean` files. There is no Mathlib dependency. Standard foundational axioms must still be stated accurately; 30 axiom-free declarations do not make all 130 axiom-free.

The regex source checks are supplemental, not a full Lean parser or a theorem-statement adequacy checker. Their current clean result plus actual source inspection supports no admitted/custom-assumption loophole in this package; compilation alone cannot assess whether prose matches statements. This audit supplies that semantic check. Production integration, source authenticity, public/secret noninterference, constant-time behavior, confidentiality, performance, and physical/scientific bridges remain separate proof and execution targets.

## Next formal work in dependency order

1. Publish the manuscript coverage ledger and fresh reproducible evidence, with the smoke test as its own gate.
2. Add named integer corollaries for the complete manuscript T2/T3/T4/T7/T8 statements, including witness existence, short-window acceptance/refusal, and the exact target quotient criterion. Reuse the existing kernel/readout results rather than re-proving unrelated versions.
3. Formalize carry/borrow/product winding identities and connect signed query decoding to a signed admitted-state API if that API is wanted.
4. Prove generalized CRT compatibility-to-existence, image/orbit structure, and capacity cardinality; then heterogeneous operator and value-quotient statements can use the right state types.
5. Add typed/partial compositional exactness with explicit admission invariants and the actual production binding contracts. Formalize reversible maps and retained data for each operation separately.
6. Keep the profinite completion and application-specific physical, statistical, cryptographic, or analytic bridges as independent formal targets. Finite arithmetic correctness is reusable upstream/downstream infrastructure, not a proof of those bridges by naming alone.
