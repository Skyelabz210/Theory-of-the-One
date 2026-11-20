import QuantumStrange
import QuantumRadialLimit
import MockCompletion
import BoundaryObservation34
import BoundaryValues34
import FKTYTheta
import QuantumTransport34
import Order34Source
import GaussianPairIntegrable
import FKTYCuspModes
import FKTYPeriodRegularity
import CoefficientEvaluation
import FifthSeventhHolomorphic
import FKTYCuspMoments
import ThirdOrderRows
import ThirdOrderTaylor
import PeriodicSmoothing
import EichlerProfile
import EichlerCuspLimit
import EichlerBoundaryValues
import FKTYThetaTransform
import EichlerPrimitive
import EichlerHorizontal
import EichlerTransportPath
import EichlerEndpointFTC
import EichlerPathLimits
import EichlerBridge
import Order34QuantumPackets
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Follow proof and definition dependencies into Mathlib and the core package.
Report each verified theorem and reject unproved assumptions anywhere in the local analytic modules. -/

open Lean Elab Command

/- The completion identity is available at each positive height. Check its application
and the exact sector classification through their public interfaces. -/
section
open MockThetaAnalytic KElimination.ShadowConvergence

example (z : ℂ) (hz : 0 < z.im) :
    xiHalf mockCompletion z = 4 * shadowSeries (integerNome z) :=
  xiHalf_mockCompletion z hz

example (r : ZMod 11) (z : ℂ) (hz : 0 < z.im) :
    xiHalf (project11 r mockCompletion) z =
      4 * shadowDegreeBin ⟨(-r).val, (-r).val_lt⟩ (integerNome z) :=
  xiHalf_project11_mockCompletion r z hz

example (r : ZMod 11) :
    (∀ z : ℂ, 0 < z.im → xiHalf (project11 r mockCompletion) z = 0) ↔
      r.val ∈ ([1, 3, 4, 5, 9] : List ℕ) :=
  xiHalf_project11_mockCompletion_eq_zero_iff r

end

section
open MockThetaAnalytic MockThetaAnalytic.BoundaryObservation34
open KElimination.QuantumRadial KElimination.ResidueSeries
open scoped MatrixGroups Topology

example (X : ℤ) :
    ((X % 30030) % 34 + 8 * ((X / 30030) % 17)) % 34 = X % 34 :=
  target34_signed_euclidean X

example (N : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) (hN : 17 ≤ N) :
    (-4) * sumBelow 510510 (fun r => uPacket ζ N 510510 r * ζ^r) = boundaryValue 17 ζ :=
  endpoint34_from_packets N ζ hζ hN

example (u : ℂ) (hu : 0 < u.im) :
    fktyTheta u = xiHalf mockCompletion (u / 24) / 2 :=
  fktyTheta_eq_xiHalf u hu

example (hFKTY : FKTYWeightHalfLaw) (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma 24)
    (hd : 0 < g 1 1) (hc : g 1 0 ≠ 0) (x : ℚ) (he : Even x.den)
    (hx : 0 < cuspDenom g x) :
    fktyPhi x - ((cuspDenom g x : ℂ) ^ (-1/2 : ℂ)) * (fktyMultiplier g)⁻¹ *
      fktyPhi (cuspAction g x) =
        fktyVerticalPeriod fktyTheta (-(g 1 1 : ℚ) / (g 1 0 : ℚ)) x :=
  hFKTY g hg hd hc x he hx

/- Check the endpoint periods, phases, branch factor, and analytic premise together. -/
example (hFKTY : FKTYWeightHalfLaw) :
    (fktyScale * integerNome (-1/816)) *
      ((-4) * sumBelow 510510 (fun r =>
        uPacket (integerNome (1/34)) 17 510510 r * integerNome (1/34)^r)) -
      (Real.sqrt (17/5) : ℂ) * ((fktyScale * integerNome (-1/240)) *
        ((-4) * sumBelow 30030 (fun r =>
          uPacket (integerNome (1/10)) 5 30030 r * integerNome (1/10)^r))) =
      fktyVerticalPeriod (fun u => xiHalf mockCompletion (u/24) / 2) (-1/24) (-1/34) :=
  boundary34_transport10_from_packets hFKTY

/- The radial transfer admits every sequence of cutoffs above its accuracy thresholds. -/
example (law : FKTYWeightHalfLaw) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1)
    (hl : Filter.Tendsto r Filter.atTop (𝓝[<] (1 : ℝ)))
    (ht : ∀ t : ℝ, 0 < t → t < 1 → HasSum
      (fun d => complexFCoeff d * ((t : ℂ) * integerNome (1/34))^d)
      (radialF ((t : ℂ) * integerNome (1/34))))
    (hb : Filter.Tendsto (fun t : ℝ => radialF ((t : ℂ) * integerNome (1/34)) +
      radialB ((t : ℂ) * integerNome (1/34))) (𝓝[<] (1 : ℝ))
        (𝓝 (boundaryValue 17 (integerNome (1/34))))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Filter.Tendsto (fun j => fPacketAtRadius (N j) 510510 (r j) (integerNome (1/34)) +
        radialB ((r j : ℂ) * integerNome (1/34))) Filter.atTop
        (𝓝 ((fktyVerticalPeriod fktyTheta (-1/24) (-1/34) + (Real.sqrt (17/5) : ℂ) *
          ((fktyScale * integerNome (-1/240)) * boundaryValue 5 (integerNome (1/10)))) /
            (fktyScale * integerNome (-1/816)))) :=
  fPackets34_tendsto_order10_period law r hr hl ht hb

/- With the coefficient series proved in the disk, the two radial laws suffice. -/
example (law : FKTYWeightHalfLaw) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1)
    (hl : Filter.Tendsto r Filter.atTop (𝓝[<] (1 : ℝ)))
    (hb : Filter.Tendsto (fun t : ℝ => radialF ((t : ℂ) * integerNome (1/34)) +
      radialB ((t : ℂ) * integerNome (1/34))) (𝓝[<] (1 : ℝ))
        (𝓝 (boundaryValue 17 (integerNome (1/34))))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Filter.Tendsto (fun j => fPacketAtRadius (N j) 510510 (r j) (integerNome (1/34)) +
        radialB ((r j : ℂ) * integerNome (1/34))) Filter.atTop
        (𝓝 ((fktyVerticalPeriod fktyTheta (-1/24) (-1/34) + (Real.sqrt (17/5) : ℂ) *
          ((fktyScale * integerNome (-1/240)) * boundaryValue 5 (integerNome (1/10)))) /
            (fktyScale * integerNome (-1/816)))) :=
  fPackets34_tendsto_order10_period_of_radial_laws law r hr hl hb

end

section
open MockThetaAnalytic MockThetaAnalytic.Order34Source KElimination.QuantumRadial

example (X : ℤ) (N34 N10 : ℕ) {ζ η : ℂ}
    (hζ : IsPrimitiveRoot ζ 34) (hη : IsPrimitiveRoot η 10)
    (h34 : 17 ≤ N34) (h10 : 5 ≤ N10) :
    translatedPacketValue ζ N34 510510 exponent34 (observe X) = ζ^X * boundaryValue 17 ζ ∧
    translatedPacketValue η N10 30030 exponent10 (observe X) = η^X * boundaryValue 5 η :=
  source_packet_endpoints X N34 N10 hζ hη h34 h10

example (X : ℤ) (N34 N10 : ℕ) (h34 : 17 ≤ N34) (h10 : 5 ≤ N10) :
    normalizedPacketDefect N34 N10 (observe X) =
        fktyVerticalPeriod (fun u => xiHalf mockCompletion (u/24) / 2) (-1/24) (-1/34) ↔
      fktyPhi (-1/34) - (Real.sqrt (17/5) : ℂ) * fktyPhi (-1/10) =
        fktyVerticalPeriod fktyTheta (-1/24) (-1/34) :=
  normalizedPacketDefect_eq_period_iff X N34 N10 h34 h10

end

section
open MockThetaAnalytic MeasureTheory Set

example (a : ℝ) (ha : 0 < a) (D : ℕ) (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1) :
    IntegrableOn (fun t => ∑' m, w m *
      ((gaussianMode a m t - gaussianMode a (m+D) t : ℝ) : ℂ)) (Ioi 0) :=
  integrableOn_gaussianMode_pair_series a ha D w hw

example : IntegrableOn (fun t : ℝ =>
    let u : ℂ := (-1/24 : ℂ) + (t : ℂ) * Complex.I
    Complex.I * fktyTheta u / ((u - (-1/34 : ℂ)) ^ (1/2 : ℂ))) (Ioi 0) :=
  integrableOn_fktyPeriod34

example (x : ℝ) (hx : x ≠ -1/24) : AnalyticAt ℝ fktyCuspPeriod x :=
  analyticAt_fktyCuspPeriod x hx

example :
    fktyPhi (-1/10) = 2 * fktyScale * fktyCuspMoment 240 (integerNome (-1/240)) ∧
    fktyPhi (-1/34) = 2 * fktyScale * fktyCuspMoment 816 (integerNome (-1/816)) :=
  ⟨fktyPhi_eq_cuspMoment10, fktyPhi_eq_cuspMoment34⟩

example (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => q^n / chi0Denominator n q) (fifthChi0 q) ∧
      HasSum (fun n : ℕ => q^(n*n) / chi0Denominator n q) (seventhF0 q) ∧
      DifferentiableAt ℂ fifthChi0 q ∧ DifferentiableAt ℂ seventhF0 q :=
  ⟨hasSum_fifthChi0 q hq, hasSum_seventhF0 q hq,
    differentiableAt_fifthChi0 q hq, differentiableAt_seventhF0 q hq⟩

example (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun d => complexFCoeff d * q^d) (radialF q) ∧
    HasSum (fun d : ℕ => ((KElimination.MockThetaFifthZero.chiCoeff d : ℤ) : ℂ) * q^d)
      (fifthChi0 q) ∧
    HasSum (fun d : ℕ => ((KElimination.MockThetaSeventh.f0Coeff d : ℤ) : ℂ) * q^d)
      (seventhF0 q) :=
  ⟨hasSum_radialF_coefficients q hq,
    hasSum_fifthChi0_coefficients q hq, hasSum_seventhF0_coefficients q hq⟩

end

section
open MockThetaAnalytic Filter Set
open scoped Topology

/- The weight and multiplier apply to the actual bilateral series on the upper half-plane. -/
example (u : ℂ) (hu : 0 < u.im) :
    fktyTheta (u / (24*u + 1)) = (24*u + 1) ^ (3/2 : ℂ) * fktyTheta u :=
  fktyTheta_lower_unipotent u hu

/- The smoothing theorem controls arbitrary zero-mean periodic weights before specialization. -/
example (L : ℕ) (hL : 0 < L) (a : ℕ → ℂ)
    (hper : ∀ n, a (n+L) = a n) (hz : ∑ n ∈ Finset.range L, a n = 0)
    (W : ℝ → ℝ) (h0 : W 0 = 1) (hc : ContinuousAt W 0)
    (ha : AntitoneOn W (Ici 0)) (hv : ConvexOn ℝ (Ici 0) W)
    (hs : ∀ h : ℝ, 0 < h → Summable (fun n : ℕ => W (n*h))) :
    Tendsto (fun h : ℝ => ∑' n : ℕ, a n * (W (n*h) : ℂ)) (𝓝[>] 0)
      (𝓝 (-(∑ n ∈ Finset.range L, (n : ℂ) * a n) / L)) :=
  tendsto_periodic_convex_smoothing L hL a hper hz W h0 hc ha hv hs

example (z : ℂ) (hz : 0 < z.im) : ‖fktyTheta z‖ ≤ (24/Real.pi) / z.im :=
  norm_fktyTheta_le_height z hz

/- Each endpoint works for both the reflected approach and the real-axis cutoff. -/
example :
    (Tendsto (fun b : ℝ => fktyEichlerTrunc (-1/34) b b) (𝓝[>] 0) (𝓝 (fktyPhi (-1/34))) ∧
     Tendsto (fun b : ℝ => fktyEichlerTrunc (-1/34) b 0) (𝓝[>] 0) (𝓝 (fktyPhi (-1/34)))) ∧
    (Tendsto (fun b : ℝ => fktyEichlerTrunc (-1/10) b b) (𝓝[>] 0) (𝓝 (fktyPhi (-1/10))) ∧
     Tendsto (fun b : ℝ => fktyEichlerTrunc (-1/10) b 0) (𝓝[>] 0) (𝓝 (fktyPhi (-1/10)))) :=
  ⟨fktyEichler_boundaryLimits34, fktyEichler_boundaryLimits10⟩

/- The cusp-specific period identity discharges the published transformation-law premise. -/
example :
    fktyPhi (-1/34) - (Real.sqrt (17/5) : ℂ) * fktyPhi (-1/10) =
      fktyVerticalPeriod fktyTheta (-1/24) (-1/34) :=
  fkty_defect34_eq_period

open KElimination.QuantumRadial Order34Source

example (X : ℤ) (N34 N10 : ℕ) (h34 : 17 ≤ N34) (h10 : 5 ≤ N10) :
    normalizedPacketDefect N34 N10 (observe X) =
      fktyVerticalPeriod (fun u => xiHalf mockCompletion (u/24) / 2) (-1/24) (-1/34) :=
  normalizedPacketDefect_eq_period_unconditional X N34 N10 h34 h10

/- FOR supplies the radial limit of f; the period transformation is proved here. -/
example (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1)
    (hl : Filter.Tendsto r Filter.atTop (𝓝[<] (1 : ℝ)))
    (hb : Filter.Tendsto (fun t : ℝ => radialF ((t : ℂ) * integerNome (1/34)) +
      radialB ((t : ℂ) * integerNome (1/34))) (𝓝[<] (1 : ℝ))
        (𝓝 (boundaryValue 17 (integerNome (1/34))))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Filter.Tendsto (fun j => fPacketAtRadius (N j) 510510 (r j) (integerNome (1/34)) +
        radialB ((r j : ℂ) * integerNome (1/34))) Filter.atTop
        (𝓝 ((fktyVerticalPeriod fktyTheta (-1/24) (-1/34) + (Real.sqrt (17/5) : ℂ) *
          ((fktyScale * integerNome (-1/240)) * boundaryValue 5 (integerNome (1/10)))) /
            (fktyScale * integerNome (-1/816)))) :=
  fPackets34_tendsto_order10_period_of_FOR r hr hl hb

end

run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`ShadowConvergence, `ShadowOperator, `ShadowProjection, `ShadowMode,
      `QuantumRadialLimit, `QuantumStrange, `ShadowGaussian, `ShadowBounds, `ShadowInfinite,
      `MockHolomorphic, `ShadowSectors, `MockCompletion, `BoundaryObservation34,
      `BoundaryValues34, `FKTYTheta, `QuantumTransport34, `Order34Source,
      `GaussianPairIntegrable, `FKTYCuspModes, `FKTYPeriodRegularity,
      `CoefficientEvaluation, `FifthSeventhHolomorphic, `FKTYCuspMoments,
      `ThirdOrderRows, `ThirdOrderTaylor,
      `PeriodicSmoothing, `EichlerProfile, `EichlerCuspLimit, `EichlerBoundaryValues,
      `FKTYThetaTransform, `EichlerPrimitive, `EichlerHorizontal, `EichlerTransportPath,
      `EichlerEndpointFTC, `EichlerPathLimits, `EichlerBridge, `Order34QuantumPackets]
  let mut audited := #[]
  for mod in modules do
    let some idx := env.getModuleIdx? mod | throwError "missing module {mod}"
    let decls := env.header.moduleData[idx]!.constants
    let mut proofs := 0
    for decl in decls do
      let axioms ← collectAxioms decl.name
      if decl.isUnsafe || decl.isPartial || axioms.any (!allowed.contains ·) then
        throwError "unverified declaration {decl.name}, axioms {axioms}"
      audited := audited.push decl.name
      if let .thmInfo thm := decl then
        let isTrivial ← liftTermElabM <| Meta.forallTelescopeReducing thm.type fun _ body => do
          return (← Meta.whnf body).isConstOf ``True
        if isTrivial then throwError "theorem {decl.name} concludes True"
        let deps := String.intercalate "," (axioms.toList.map toString).mergeSort
        logInfo m!"THEOREM {mod} {decl.name} [{deps}]"
        proofs := proofs + 1
    if proofs == 0 then throwError "no theorems audited in {mod}"
    logInfo m!"MODULE {mod} {proofs} {decls.size}"
  let required := #[``KElimination.ShadowConvergence.upperHalfPlane_shadow,
      ``KElimination.ShadowConvergence.shadowSeries_eq_sum_degreeBins,
      ``MockThetaAnalytic.xiHalf, ``MockThetaAnalytic.xiHalf_const_mul,
      ``MockThetaAnalytic.xiHalf_real_translate, ``MockThetaAnalytic.xiHalf_project11,
      ``MockThetaAnalytic.hasDerivAt_erfc, ``MockThetaAnalytic.xiHalf_nonholomorphicMode,
      ``MockThetaAnalytic.finiteHolomorphicPart, ``MockThetaAnalytic.finiteCompletion,
      ``MockThetaAnalytic.xiHalf_finiteCompletion, ``MockThetaAnalytic.tendsto_xiHalf_finiteCompletion,
      ``MockThetaAnalytic.project11_monomial, ``MockThetaAnalytic.project11_shadowSeries,
      ``MockThetaAnalytic.project11_xiShadowSeries, ``MockThetaAnalytic.xiHalf_project11_of_shadow,
      ``MockThetaAnalytic.for_limit_from_f_packets,
      ``MockThetaAnalytic.uOnePartial_stable, ``MockThetaAnalytic.strangeCusp,
      ``MockThetaAnalytic.strangeCusp_eq_partial, ``MockThetaAnalytic.strangeCusp_add_one,
      ``MockThetaAnalytic.hasSum_uOne, ``MockThetaAnalytic.strangeCusp_eq_tsum,
      ``MockThetaAnalytic.strangeCusp_half, ``MockThetaAnalytic.strangeValue_eleven,
      ``MockThetaAnalytic.strangeCusp_eleventh,
      ``MockThetaAnalytic.erfc_eq_tail_integral, ``MockThetaAnalytic.erfc_nonneg,
      ``MockThetaAnalytic.abs_erfc_le, ``MockThetaAnalytic.hasDerivAt_modeAmplitude,
      ``MockThetaAnalytic.modeMajorant, ``MockThetaAnalytic.modeMajorant_summable,
      ``MockThetaAnalytic.norm_signedMode_le, ``MockThetaAnalytic.norm_fderiv_signedMode_le,
      ``MockThetaAnalytic.differentiableAt_signedMode,
      ``MockThetaAnalytic.summable_nonholomorphicModes,
      ``MockThetaAnalytic.hasFDerivAt_nonholomorphicPart,
      ``MockThetaAnalytic.differentiableAt_nonholomorphicPart,
      ``MockThetaAnalytic.xiHalf_nonholomorphicPart, ``MockThetaAnalytic.normalizedF,
      ``MockThetaAnalytic.summable_radialFTerm, ``MockThetaAnalytic.hasSum_radialF,
      ``MockThetaAnalytic.differentiableAt_radialF, ``MockThetaAnalytic.differentiableAt_normalizedF,
      ``MockThetaAnalytic.shadowDegreeBin_identically_zero_iff, ``MockThetaAnalytic.mockCompletion,
      ``MockThetaAnalytic.differentiableAt_mockCompletion, ``MockThetaAnalytic.xiHalf_mockCompletion,
      ``MockThetaAnalytic.xiHalf_project11_mockCompletion,
      ``MockThetaAnalytic.xiHalf_project11_mockCompletion_eq_zero_iff,
      ``MockThetaAnalytic.BoundaryObservation34.target10_primary,
      ``MockThetaAnalytic.BoundaryObservation34.target34_recoverable_iff,
      ``MockThetaAnalytic.BoundaryObservation34.target34_projection,
      ``MockThetaAnalytic.BoundaryObservation34.target34_signed_euclidean,
      ``MockThetaAnalytic.BoundaryObservation34.target34_from_anchor17,
      ``MockThetaAnalytic.BoundaryObservation34.primary_only_witness,
      ``MockThetaAnalytic.BoundaryObservation34.target34_coupled_iff,
      ``MockThetaAnalytic.BoundaryObservation34.target34_minimal_primary_multiple,
      ``MockThetaAnalytic.BoundaryObservation34.order34_outside_primary_powers,
      ``MockThetaAnalytic.BoundaryObservation34.endpoint10_from_packets,
      ``MockThetaAnalytic.BoundaryObservation34.endpoint34_from_packets,
      ``MockThetaAnalytic.fktyTheta_eq_shadowSeries, ``MockThetaAnalytic.fktyTheta_eq_xiHalf,
      ``MockThetaAnalytic.fktyThetaTerm_summable, ``MockThetaAnalytic.fktyThetaTerm_eq_exp,
      ``MockThetaAnalytic.fktyChi12_period, ``MockThetaAnalytic.fktyPhi_neg_one_div_34,
      ``MockThetaAnalytic.fktyPhi_neg_one_div_10, ``MockThetaAnalytic.boundaryValue_cyclotomic34,
      ``MockThetaAnalytic.boundaryValue_cyclotomic10,
      ``MockThetaAnalytic.hasSum_fNegPartial, ``MockThetaAnalytic.fktyPhi_eq_tsum,
      ``MockThetaAnalytic.fktyPhi_add_one,
      ``MockThetaAnalytic.fNegPartial_reflection17, ``MockThetaAnalytic.fNegPartial_reflection5,
      ``MockThetaAnalytic.transportMatrix34_mem, ``MockThetaAnalytic.transportMatrix34_cusps,
      ``MockThetaAnalytic.transportMatrix34_multiplier, ``MockThetaAnalytic.transportMatrix34_weight,
      ``MockThetaAnalytic.FKTYWeightHalfLaw, ``MockThetaAnalytic.boundary34_transport10,
      ``MockThetaAnalytic.fktyPeriod34_eq_completionPeriod,
      ``MockThetaAnalytic.boundary34_transport10_from_packets,
      ``MockThetaAnalytic.boundary34_from_period_and_ten,
      ``MockThetaAnalytic.fPackets34_tendsto_order10_period,
      ``MockThetaAnalytic.Order34Source.source_readout,
      ``MockThetaAnalytic.Order34Source.source_readout_agrees_with_anchor,
      ``MockThetaAnalytic.Order34Source.quotient17_of_observed_source,
      ``MockThetaAnalytic.Order34Source.no_primary_quotient17,
      ``MockThetaAnalytic.Order34Source.source_phase_shift,
      ``MockThetaAnalytic.Order34Source.no_primary_phase34,
      ``MockThetaAnalytic.Order34Source.translatedPacketValue,
      ``MockThetaAnalytic.Order34Source.source_packet_endpoints,
      ``MockThetaAnalytic.Order34Source.normalizedPacketDefect,
      ``MockThetaAnalytic.Order34Source.normalizedPacketDefect_eq_boundary,
      ``MockThetaAnalytic.Order34Source.normalizedPacketDefect_eq_period_iff,
      ``MockThetaAnalytic.Order34Source.normalizedPacketDefect_eq_period,
      ``MockThetaAnalytic.integrableOn_gaussianMode,
      ``MockThetaAnalytic.integral_norm_gaussianMode_sub_le,
      ``MockThetaAnalytic.integrableOn_gaussianMode_pair_series,
      ``MockThetaAnalytic.fktyCuspPhase_add_144, ``MockThetaAnalytic.norm_fktyCuspPhase_le_one,
      ``MockThetaAnalytic.summable_fktyCuspModes, ``MockThetaAnalytic.fktyTheta_cusp,
      ``MockThetaAnalytic.fktyTheta_cusp_paired,
      ``MockThetaAnalytic.integrableOn_fktyTheta_cusp,
      ``MockThetaAnalytic.integrableOn_fktyPeriod34,
      ``MockThetaAnalytic.analyticAt_fktyCuspPeriod, ``MockThetaAnalytic.fktyVerticalKernel_eq_rotated,
      ``MockThetaAnalytic.fktyCuspPeriod_rat,
      ``MockThetaAnalytic.fktyPhi_defect_eq_cuspPeriod,
      ``MockThetaAnalytic.fifthChi0_seventhF0_factors, ``MockThetaAnalytic.fifthChi0,
      ``MockThetaAnalytic.seventhF0,
      ``MockThetaAnalytic.hasSum_fifthChi0, ``MockThetaAnalytic.hasSum_seventhF0,
      ``MockThetaAnalytic.hasSum_fifthChi0_coefficients,
      ``MockThetaAnalytic.hasSum_seventhF0_coefficients,
      ``MockThetaAnalytic.differentiableAt_fifthChi0, ``MockThetaAnalytic.differentiableAt_seventhF0,
      ``MockThetaAnalytic.fktyPhi_eq_cuspMoment34, ``MockThetaAnalytic.fktyPhi_eq_cuspMoment10,
      ``MockThetaAnalytic.fktyCuspCoefficient_period, ``MockThetaAnalytic.sum_fktyCuspCoefficient_eq_zero,
      ``MockThetaAnalytic.thirdOrderRow, ``MockThetaAnalytic.thirdOrderRowNorm,
      ``MockThetaAnalytic.CoefficientEvaluation.eval_divide,
      ``MockThetaAnalytic.CoefficientEvaluation.hasSum_shifted_family,
      ``MockThetaAnalytic.mockSquareBound, ``MockThetaAnalytic.summable_mockSquareBound,
      ``MockThetaAnalytic.hasSum_radialF_coefficients,
      ``MockThetaAnalytic.for_limit_from_f_packets_of_radial_law,
      ``MockThetaAnalytic.fPackets34_tendsto_order10_period_of_radial_laws,
      ``MockThetaAnalytic.tendsto_periodic_convex_smoothing, ``MockThetaAnalytic.eichlerProfile,
      ``MockThetaAnalytic.eichlerProfile_zero, ``MockThetaAnalytic.eichlerProfile_nonneg,
      ``MockThetaAnalytic.deriv2_eichlerProfile, ``MockThetaAnalytic.continuous_eichlerProfile,
      ``MockThetaAnalytic.convexOn_eichlerProfile, ``MockThetaAnalytic.antitoneOn_eichlerProfile,
      ``MockThetaAnalytic.tendsto_eichlerProfile_atTop,
      ``MockThetaAnalytic.summable_eichlerProfile_mesh, ``MockThetaAnalytic.erfc_zero,
      ``MockThetaAnalytic.continuous_erfc, ``MockThetaAnalytic.antitoneOn_erfc,
      ``MockThetaAnalytic.convexOn_erfc, ``MockThetaAnalytic.tendsto_erfc_atTop,
      ``MockThetaAnalytic.summable_erfc_mesh, ``MockThetaAnalytic.fktyEichlerIntegrand,
      ``MockThetaAnalytic.fktyEichlerTrunc, ``MockThetaAnalytic.fktyTheta_ray,
      ``MockThetaAnalytic.integrableOn_fktyEichlerTrunc,
      ``MockThetaAnalytic.fktyEichlerTrunc_eq_series,
      ``MockThetaAnalytic.fktyEichlerTrunc_eq_lower_series,
      ``MockThetaAnalytic.fktyEichlerTrunc_eq_boundary_series,
      ``MockThetaAnalytic.fktyEichler_boundaryLimits_of_period,
      ``MockThetaAnalytic.fktyEichler_boundaryLimits34,
      ``MockThetaAnalytic.fktyEichler_boundaryLimits10,
      ``MockThetaAnalytic.fktyTheta_eq_shiftedJacobi, ``MockThetaAnalytic.fktyTheta_lower_unipotent,
      ``MockThetaAnalytic.isExactOn_upperHalf, ``MockThetaAnalytic.differentiableAt_fktyTheta,
      ``MockThetaAnalytic.eichlerForm, ``MockThetaAnalytic.exists_eichlerPrimitive,
      ``MockThetaAnalytic.hasDerivAt_eichlerPrimitive_vertical,
      ``MockThetaAnalytic.norm_fktyTheta_le_height, ``MockThetaAnalytic.norm_horizontal_bridge_le,
      ``MockThetaAnalytic.eichlerTransportMap, ``MockThetaAnalytic.eichlerTargetRay,
      ``MockThetaAnalytic.eichlerInverseRay, ``MockThetaAnalytic.eichlerRayDenom,
      ``MockThetaAnalytic.eichlerInverseRay_coordinates,
      ``MockThetaAnalytic.eichlerInverseRay_im_pos,
      ``MockThetaAnalytic.eichlerTransportMap_inverseRay,
      ``MockThetaAnalytic.eichlerInverseRay_hasDerivAt,
      ``MockThetaAnalytic.eichlerInverseRay_offset_zero,
      ``MockThetaAnalytic.eichlerInverseRay_offset_infty,
      ``MockThetaAnalytic.eichlerInverseRay_height_zero,
      ``MockThetaAnalytic.eichlerInverseRay_height_infty,
      ``MockThetaAnalytic.eichlerInverseRay_pullback,
      ``MockThetaAnalytic.hasDerivAt_eichlerPrimitive_inverseRay,
      ``MockThetaAnalytic.tendsto_eichlerTail_zero, ``MockThetaAnalytic.primitive_ray_endpoints,
      ``MockThetaAnalytic.eichlerPrimitive_vertical_gap_top,
      ``MockThetaAnalytic.eichlerPrimitive_inverseRay_gap_zero,
      ``MockThetaAnalytic.eichlerPrimitive_inverseRay_gap_infty,
      ``MockThetaAnalytic.fkty_defect34_eq_period,
      ``MockThetaAnalytic.boundary34_from_period_and_ten_unconditional,
      ``MockThetaAnalytic.normalizedPacketDefect_eq_period_unconditional,
      ``MockThetaAnalytic.fPackets34_tendsto_order10_period_of_FOR]
  unless required.all audited.contains do throwError "required public result missing from the audit"
  logInfo m!"PASS analytic audit: {audited.size} declarations in {modules.size} modules"
