# Proof map

Paths start at the Theory-of-the-One root. Read each declaration at the revision being cited. The [analytic audit receipt](../../../../adapters/MockThetaAnalytic/verification.json) records the source hashes and axiom dependencies for that revision.

## Source observation and finite evaluation

For the next experiment and the checked failure of the common-resolution definition of family order, see the [research handoff](../../../../docs/reviews/2026-11-24-cram-research-handoff.md) and the [standalone order test](../../../../formal/controls/OrderTest.lean).

| Result | Lean route | Contract |
| --- | --- | --- |
| Exact recovery from coupled anchors | `formal/universal/CoupledAnchors.lean` → `source_period`, `resolution_eq_lcm_reduced`. `formal/universal/ProfiniteObservations.lean` → `combined_target_fiber_constant_iff`, `combined_target_recoverable_iff` | Positive target and anchors, same source in the signed chart. Reuse the fiber criterion before constructing a decoder. |
| Signed quotient readout | `formal/universal/StarLift.lean` → `negative_query_of_decomposition`, `positive_adjacent_congruence`, `negative_nonunit_chart_query` | Read the sign convention, inverse certificate and actual reduced modulus. Recover an integer representative when the readings isolate one value in the admitted domain. |
| Compatible coordinates and finite packets | `formal/universal/ProfiniteObservations.lean` → `cylinder_fiber_constant`, `refined_cylinder_fiber_constant`. `formal/universal/ResidueSeries.lean` → `packet_refinement`, `finite_root_evaluation` | Coarse packets sum over finer classes. Evaluation uses the entire finite packet distribution and a period through which the character factors. |
| All seventeen original series | `formal/universal/MockTheta.lean` → `mockTheta_from_coupled_anchors`. See `MockThetaPhi.lean`, `MockThetaPsi.lean`, `MockThetaChi.lean`, `MockThetaFifthZero.lean`, `MockThetaFifthOne.lean`, and `MockThetaSeventh.lean` in the same directory. | Coefficient construction and finite evaluation. The two fifth-order groups and the seventh-order group each expose `from_coupled_anchors`. |
| Partition crank modulo 11 | `formal/universal/PartitionCrank11.lean` → `crank_histogram_six`, `rank_histogram_six`. `formal/universal/CrankCharacter11.lean` → `crank_six_vanishes`, `seventh_crank_from_s8` | The partitions of six give one crank per class and empty rank classes 4 and 7. For seventh-order weights, verify `hobs` for each retained partition, including `after = before + splitPayload * crank`. |

Check the machine representation and source binding against `docs/ARCHITECTURE.md`. The finite packet theorem yields the truncated evaluation \(\sum_{d<N}a_d(tz)^d\) from the weighted residue bins when \(z^b=1\) and \(b\mid L\). For the family classification and source history, consult `evidence/STATUS.md` alongside the current source.

## Differential shadow and period

All paths in this table are under `adapters/MockThetaAnalytic/`.

| Result | Lean route | Contract |
| --- | --- | --- |
| Infinite completion of \(f\) | `MockCompletion.lean` → `xiHalf_mockCompletion`, `xiHalf_project11_mockCompletion_eq_zero_iff` | Holomorphic part \(q^{-1}f(q^{24})\) plus the nonholomorphic correction, \(q=e^{2\pi iz}\), \(\Im z>0\). The differential is \(4\) times the unary shadow series. Completion sectors \(1,3,4,5,9\) have identically zero shadow. |
| Recover shadow from coefficients | `ShadowReadings.lean` → `reciprocal_fiber_constant`. `ShadowReconstruction.lean` → `mock_shadowMode_eq_cutoff`, `mock_reconstruct_xiHalf_uniform` | Use a unit constant term and retain every public degree through \(D\). Parity, Euler reciprocal and signed eta lift recover Fourier modes through \(24D+1\). |
| Arithmetic Hecke square | `ShadowHecke.lean` → `hecke_moment`, `crank_basis_transport`, `size_three_fixed_mask_fails`. `ShadowReconstruction.lean` → `mock_hecke_prefix`, `mock_hecke_uniform` | Lean verifies the finite stencil and its limit. The identification with the geometric Hecke operators uses the modular-form results cited in `docs/reviews/2026-11-21-cram-shadow-reconstruction.md`. |
| Period from recovered prefixes | `ShadowPeriod.lean` → `recoveredPeriod_uniform`, `recoveredPeriod_tendsto_normalizedPacketDefect`. `ShadowEndpoint.lean` → `averagedFullPeriod_uniform`, `rawFullPeriod_cusp_no_limit`. `ShadowEndpointValue24.lean` → `averagedFullPeriod_eq_fktyPhi24` | Use the uniformity hypothesis away from \(-1/24\) for the raw cutoff. Use the two-cutoff average through the starting cusp itself. |
| Radial limits and FKTY scale | `ThirdOrderTaylor.lean`. `FOREvenRoot.lean` → `radialF_compensated_tendsto_boundary_of_half_power`, `fPackets_tendsto_boundary_from_coupled_anchors`, `normalized_fPackets_tendsto_fkty`. `FKTYReflection.lean` → `fktyPhi_reflected_boundary` | The radial theorem admits \(\zeta^k=-1\). The coupled packet theorem takes a primitive root of order \(2k\). For rational \(x\) of reduced denominator \(2k\), use \(\zeta=e^{-2\pi ix}\) and `fktyScale * integerNome ((x : ℂ)/24)`. |
| Order-34 to order-10 transport | `Order34Source.lean` → `quotient17_of_observed_source`, `no_primary_phase34`. `Order34QuantumPackets.lean` → `normalizedPacketDefect_eq_period_unconditional`. `FOROrder34.lean` → `fPackets34_tendsto_order10_period_unconditional` | The auxiliary mod-17 observation is defined for every signed source. Supply that reading and the actual coefficient packets in an implementation. The analytic identity includes the Eichler period correction. |
| Order-34 endpoint at a requested precision | `ShadowPeriod.lean` → `recoveredTranslatedBoundary34_error`, `recoveredTranslatedBoundary34_tolerance` | Supply the authentic S6 prefix through the inclusive degree, the source lanes, and stabilized order-10 packets. For positive rational tolerance \(a/b\), use degree at least \(2{,}457{,}600\lceil b/a\rceil^2\). The bound covers truncation of the exact finite integral. |

Use `adapters/MockThetaAnalytic/README.md` for adjacent results, including interior Taylor sums and holomorphy for \(\chi_0\) and \(\mathcal F_0\). For the two-variable specialization at \(w=1\), follow `QuantumStrange.lean` and `strangeCusp_add_one` for the separate weight-\(3/2\) translation law. For attribution, use the citations to Zwegers, Folsom–Ono–Rhoades, Folsom, Ki, Truong Vu and Yang (FKTY), and Lovejoy in the repository reviews.

## Reusable phase controls

| Target phase order | Primary \(M\) | Required \(H\) | Anchor fixture | Retained period \(L\) |
| --- | ---: | ---: | --- | ---: |
| 10 | 30030 | 1 | empty | 30030 |
| 22 | 2730, with 11 removed for the control | 11 | same-source 11 | 30030 |
| 24 | 30030 | 4 | same-source 8 | 120120 |
| 34 | 30030 | 17 | same-source 17 | 510510 |
| 44 | 30030 | 2 | same-source 4 | 60060 |

The order-34 primary-only collision is \(X=0,30030\). The order-24 mod-4 anchor supplies \(H=2\), so \(X\) and \(X+60060\) match the readings and differ in phase. Check `FOREvenRoot.lean` for `coupled_phase_fiber_constant_iff` and `order22_shadow_anchor`, and `FOROrder24.lean` for `anchor_resolutions` and `least_order24_packet_period`.

## Watson congruence and multiplicity

Use `adapters/MockThetaAnalytic/FORWatsonCongruence.lean` for `watson_polynomial_congruence`, `watson_cleared_eq_of_half_power` and `watson_even_polynomial_congruence`. Read `docs/reviews/2026-11-22-cram-even-roots.md` for the derivation. The complex root proof identifies the finite Newton transform at the roots and uses monic integer division to establish a vanishing remainder. At an even \(k\), reversal at the roots of \(X^s+1\) for odd \(s\mid k\) gives the additional integer divisor. Coefficient reduction commutes with the cleared expression by `map_watsonCongruenceDifference`.

For direct coefficient experiments, start with \(W_{c,0}=0\), \(D_{c,0}=1\), and append \(F_n=1+X^{2n+c}\). The recurrences are \(W_{c,n+1}=(W_{c,n}+(-X)^{n^2})F_n\) and \(D_{c,n+1}=D_{c,n}F_n\). Choose \(c=1\) and \(B_k=1+U_k\) for even \(k\), or \(c=2\) and \(B_k=-2U_k\) for odd \(k\). Here \(U_k\) is `uPartial` in `formal/universal/QuantumRadial.lean`. For small characteristic, compute Taylor coefficients directly in \(Y=X+1\) or use monic division to measure multiplicity.

Use `adapters/MockThetaAnalytic/FORWatsonMultiplicity.lean` for the local coefficients at \(-1\). For odd \(k\), the quotient \(Q_k=\Delta_k/(X^k+1)\) has \(Q_k(-1)=2(k+1)\). For odd \(k\ge3\), it has \(Q_k'(-1)=-(k^3+k^2+3k+6)\). For even \(k>0\), \(\Delta'_k(-1)=2k\), so the cofactor for odd \(s\mid k\) has value \(2k/s\). In odd prime characteristic the Frobenius power gives repeated factors and a nonzero cofactor certifies sharpness. Use `watson_rootMultiplicity_at_neg_one` for the full \(p>3\) theorem.

Modulo 11, the double class is \(k\equiv21\bmod22\). The inputs \(11,121\) have the same class mod 22 and multiplicities \(11,121\). When a reader needs the exponent \(e=v_{11}(k)\) in the divisible class, check the zero residue modulo \(11^e\) and a nonzero residue modulo \(11^{e+1}\).
