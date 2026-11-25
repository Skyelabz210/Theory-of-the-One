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
import FORRadialProducts
import FORCyclotomicBlock
import FORPhiRadial
import FineRank
import FORGaussFinite
import FORRadialIdentity
import FORPhiProduct
import FORRankProduct
import FORGaussLimit
import FOROrder34
import FOROrder24
import FOREvenRoot
import FORWatsonMultiplicity
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

/- Compatibility with the earlier packet transfer, which accepts a supplied radial limit. -/
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

/- Watson's disk identity and the actual FOR boundary value at every primitive 34th root. -/
example (q : ℂ) (hq : ‖q‖ < 1) : radialF q + radialB q = 2 * watsonPhi q :=
  watson_compensated_identity q hq

example (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) :
    Tendsto (fun t : ℝ => radialF ((t : ℂ)*ζ) + radialB ((t : ℂ)*ζ))
      (𝓝[<] 1) (𝓝 (boundaryValue 17 ζ)) :=
  radialF_add_radialB_tendsto_order34 ζ hζ

/- With only the radial path supplied, the packet truncations converge to the shadow period formula. -/
example (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1)
    (hl : Filter.Tendsto r Filter.atTop (𝓝[<] (1 : ℝ))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Filter.Tendsto (fun j => fPacketAtRadius (N j) 510510 (r j) (integerNome (1/34)) +
        radialB ((r j : ℂ) * integerNome (1/34))) Filter.atTop
        (𝓝 ((fktyVerticalPeriod fktyTheta (-1/24) (-1/34) + (Real.sqrt (17/5) : ℂ) *
          ((fktyScale * integerNome (-1/240)) * boundaryValue 5 (integerNome (1/10)))) /
            (fktyScale * integerNome (-1/816)))) :=
  fPackets34_tendsto_order10_period_unconditional r hr hl

end

section
open MockThetaAnalytic KElimination.MockTheta KElimination.QuantumRadial
open ShadowPeriod
open scoped Topology

example (X : ℤ) (N34 N10 : ℕ) (h34 : 17 ≤ N34) (h10 : 5 ≤ N10) :
    Filter.Tendsto
      (fun D => recoveredPeriod (ShadowReadings.observe D mockCoeff) (fun _ => 1) (-1/34))
      Filter.atTop (𝓝 (Order34Source.normalizedPacketDefect N34 N10 (Order34Source.observe X))) :=
  recoveredPeriod_tendsto_normalizedPacketDefect X N34 N10 h34 h10

example : Filter.Tendsto (fun D => recoveredBoundary34 (ShadowReadings.observe D mockCoeff))
    Filter.atTop (𝓝 (boundaryValue 17 (integerNome (1/34)))) :=
  recoveredBoundary34_tendsto

example : ‖recoveredTranslatedBoundary34 (ShadowReadings.observe 0 mockCoeff)
    (Order34Source.observe (-1)) 5 -
    Order34Source.translatedPacketValue (integerNome (1/34)) 17 510510
      Order34Source.exponent34 (Order34Source.observe (-1))‖ ≤ 7680 := by
  simpa using recoveredTranslatedBoundary34_error 0 (-1) 17 5 (by decide) (by decide)

example (n : ℕ) (hn : 0 < n) (X : ℤ) :
    ‖recoveredTranslatedBoundary34 (ShadowReadings.observe (boundary34Degree n) mockCoeff)
      (Order34Source.observe X) 5 - Order34Source.translatedPacketValue (integerNome (1/34))
        17 510510 Order34Source.exponent34 (Order34Source.observe X)‖ ≤ 1 / (n : ℝ) :=
  recoveredTranslatedBoundary34_precision _ n X 17 5 hn le_rfl (by decide) (by decide)

example : boundary34ToleranceDegree 2 3 = boundary34Degree 2 := by decide

example : (0 : ℤ) % 30030 = 30030 % 30030 ∧
    Order34Source.exponent10 (Order34Source.observe 0) =
      Order34Source.exponent10 (Order34Source.observe 30030) ∧
    Order34Source.exponent34 (Order34Source.observe 0) ≠
      Order34Source.exponent34 (Order34Source.observe 30030) := by decide

example : ShadowEndpoint.averagedPeriod (ShadowReadings.observe 852 mockCoeff) (fun _ => 1)
    144 (-1/24) = fktyPhi (-1/24) := by
  apply ShadowEndpoint.averagedFullPeriod_eq_fktyPhi24
  have h : 143 ≤ (24*852+1 : ℕ).sqrt := Nat.le_sqrt.mpr (by decide)
  exact Nat.succ_le_succ h

example (X : ℤ) : Order24Source.normalizedPacket24 12 (Order24Source.observe X) =
    ShadowEndpoint.averagedPeriod (ShadowReadings.observe 852 mockCoeff) (fun _ => 1) 144 (-1/24) := by
  apply Order24Source.normalizedPacket24_eq_averaged X 12 852 (by decide)
  have h : 143 ≤ (24*852+1 : ℕ).sqrt := Nat.le_sqrt.mpr (by decide)
  exact Nat.succ_le_succ h

example (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 22) (r : ℕ → ℝ)
    (hr : ∀ j, 0 < r j ∧ r j < 1) (hl : Filter.Tendsto r Filter.atTop (𝓝[<] (1:ℝ))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Filter.Tendsto (fun j => fPacketAtRadius (N j) 30030 (r j) ζ + radialB ((r j:ℂ)*ζ))
        Filter.atTop (𝓝 (boundaryValue 11 ζ)) := by
  have h := fPackets_tendsto_boundary_from_coupled_anchors (ζ := ζ) (k := 11) (M := 2730)
    (by decide) hζ (by decide) [11] (by simp) (by decide) r hr hl
  have hs : (-1:ℂ)^11 = -1 := by norm_num
  simpa only [hs, neg_one_mul, sub_neg_eq_add, show
    2730 * KElimination.CoupledAnchors.resolution 2730 [11] = 30030 by decide] using h

example (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 44) (r : ℕ → ℝ)
    (hr : ∀ j, 0 < r j ∧ r j < 1) (hl : Filter.Tendsto r Filter.atTop (𝓝[<] (1:ℝ))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Filter.Tendsto (fun j => fPacketAtRadius (N j) 60060 (r j) ζ - radialB ((r j:ℂ)*ζ))
        Filter.atTop (𝓝 (boundaryValue 22 ζ)) := by
  have h := fPackets_tendsto_boundary_from_coupled_anchors (ζ := ζ) (k := 22) (M := 30030)
    (by decide) hζ (by decide) [4] (by simp) (by decide) r hr hl
  have hs : (-1:ℂ)^22 = 1 := by norm_num
  simpa only [hs, one_mul, show
    30030 * KElimination.CoupledAnchors.resolution 30030 [4] = 60060 by decide] using h

example : watsonBoundaryCertificate 1001 = true := watsonBoundaryCertificate_all (by decide)

open Polynomial in
example : watsonCongruenceDifference 1 (X : ℤ[X]) = (X+1)*(2*X^2-X+1) ∧
    ¬ (X+1 : ℤ[X])^2 ∣ watsonCongruenceDifference 1 X := by
  have h : watsonCongruenceDifference 1 (X : ℤ[X]) = (X+1)*(2*X^2-X+1) := by
    norm_num [watsonCongruenceDifference, watsonClearedNumerator, watsonDen,
      Finset.sum_range_succ, Finset.prod_range_succ, uPartial, uPolynomial,
      KElimination.ResidueSeries.sumBelow, uProduct]
    ring
  refine ⟨h, ?_⟩
  rw [h, pow_two, mul_dvd_mul_iff_left (by simpa using X_add_C_ne_zero (1:ℤ))]
  intro hdvd
  have hz := eval_eq_zero_of_dvd_of_eval_eq_zero hdvd (by simp : (X+1 : ℤ[X]).eval (-1) = 0)
  norm_num at hz

-- The denominator vanishes in this composite residue ring and the cleared sum is 6.
example : watsonDen (-1 : ZMod 8) 2 3 = 0 ∧ watsonClearedNumerator (-1 : ZMod 8) 2 3 = 6 := by
  have hD : watsonDen (-1 : ZMod 8) 2 3 = 0 := by decide +kernel
  have hU : uPartial 3 (-1 : ZMod 8) = -1 := by decide +kernel
  refine ⟨hD, ?_⟩
  have h := watson_cleared_eq_of_half_power (by decide : (-1 : ZMod 8)^3 = -1)
  simp only [if_neg (by decide : ¬ Even 3), hD, hU] at h
  exact h.trans (by decide)

open Polynomial in
example : (X+1 : (ZMod 11)[X])^11 ∣ watsonCongruenceDifference 11 X := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  simpa using watson_congruence_prime_power 11 1 1 (X : (ZMod 11)[X])

section
open Polynomial

example : (watsonQuotient 11).eval (-1) = 24 := by
  rw [watson_quotient_at_neg_one (by decide : Odd 11)]
  norm_num

example : (watsonCongruenceDifference 11 (X : (ZMod 11)[X])).rootMultiplicity (-1) = 11 ∧
    (watsonCongruenceDifference 33 (X : (ZMod 11)[X])).rootMultiplicity (-1) = 11 ∧
    (watsonCongruenceDifference 121 (X : (ZMod 11)[X])).rootMultiplicity (-1) = 121 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact ⟨watson_rootMultiplicity_odd_prime 11 1 1 (by decide) (by decide) (by decide) (by decide),
    watson_rootMultiplicity_odd_prime 11 3 1 (by decide) (by decide) (by decide) (by decide),
    watson_rootMultiplicity_odd_prime 11 1 2 (by decide) (by decide) (by decide) (by decide)⟩

-- The derivative 264 reduces to 22 modulo 121, where the same root is simple.
example : (watsonCongruenceDifference 11 (X : (ZMod 121)[X])).rootMultiplicity (-1) = 1 :=
  watson_rootMultiplicity_one_of_nonzero_slope (by decide : Odd 11) (by decide)

-- Here the quotient itself vanishes at −1 in characteristic 11.
example : (X^21+1)*(X+1 : (ZMod 11)[X]) ∣ watsonCongruenceDifference 21 X :=
  (watson_extra_linear_factor_iff (by decide : Odd 21)).mpr (by decide)

example : (X^11+1 : ℤ[X]) ∣ watsonCongruenceDifference 22 X :=
  watson_even_polynomial_congruence (by decide) (by decide) (by decide) (by decide)

example : (watsonQuotient 21).derivative.eval (-1) = -9771 := by
  rw [watson_quotient_derivative_at_neg_one (by decide : Odd 21) (by decide)]
  norm_num

-- The uniform theorem covers simple roots, the k+1 branch, and both parities.
example : (watsonCongruenceDifference 17 (X : (ZMod 11)[X])).rootMultiplicity (-1) = 1 ∧
    (watsonCongruenceDifference 21 (X : (ZMod 11)[X])).rootMultiplicity (-1) = 2 ∧
    (watsonCongruenceDifference 22 (X : (ZMod 11)[X])).rootMultiplicity (-1) = 11 ∧
    (watsonCongruenceDifference 242 (X : (ZMod 11)[X])).rootMultiplicity (-1) = 121 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h17 := watson_rootMultiplicity_at_neg_one (by decide : 3 < 11) (by decide : 0 < 17)
  have h21 := watson_rootMultiplicity_at_neg_one (by decide : 3 < 11) (by decide : 0 < 21)
  have h22 := watson_rootMultiplicity_at_neg_one (by decide : 3 < 11) (by decide : 0 < 22)
  have h242 := watson_rootMultiplicity_at_neg_one (by decide : 3 < 11) (by decide : 0 < 242)
  have hp : Nat.Prime 11 := Fact.out
  have hval (e : ℕ) : (11^e*2).factorization 11 = e := by
    rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) (by decide), hp.factorization_pow,
      Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 11 ∣ 2), add_zero]
  refine ⟨h17.trans ?_, h21.trans (by decide), h22.trans ?_, h242.trans ?_⟩
  · rw [if_neg (by decide), Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 11 ∣ 17), pow_zero]
  · rw [if_neg (by decide), show (22:ℕ) = 11^1*2 by decide, hval, pow_one]
  · rw [if_neg (by decide), show (242:ℕ) = 11^2*2 by decide, hval]
    decide

example : (watsonCongruenceDifference 21 (X : (ZMod 121)[X])).rootMultiplicity (-1) = 1 ∧
    (watsonCongruenceDifference 241 (X : (ZMod 121)[X])).rootMultiplicity (-1) = 2 :=
  ⟨watson_rootMultiplicity_one_of_nonzero_slope (by decide : Odd 21) (by decide),
    watson_rootMultiplicity_two_of_cast_eq_neg_one (by decide : Odd 241) (by decide) (by decide) (by decide)⟩

end

-- In the X^12+1 quotient an eighth root gives three denominator blocks.
example (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 8) :
    8 * (∑ j ∈ Finset.range 12, watsonTerm 1 ζ j) = 7 * (1 + uPartial 4 ζ) := by
  have hq4 := primitive_even_half_power (k := 4) (by decide) hζ
  have hq12 : ζ^12 = -1 := by rw [show 12 = 4*3 by decide, pow_mul, hq4]; norm_num
  have hD := watson_denominator_blocks (c := 1) (h := 4) (by decide) hζ (by decide) 3
  change (∏ j ∈ Finset.range 12, (1+ζ^(2*j+1))) = (2:ℂ)^3 at hD
  have hU : uPartial 12 ζ = uPartial 4 ζ := uPolynomial_stable 12 4 ζ ζ (by decide) hq4 (by decide)
  have h := watson_cleared_identity hq12
  simp only [watsonClearedDifference, if_pos (by decide : Even 12), hD, hU] at h
  linear_combination h

-- Q=1 has Q²=1 but is imprimitive at k=2. The Newton identity fails there.
example : (∑ n ∈ Finset.range 2, pochhammer (2:ℂ) 1 n * (1:ℂ)^n) ≠
    (2:ℂ)^(2-1:ℕ)*∑ n ∈ Finset.range 2, (pochhammer (2:ℂ) 1 n / ((2:ℂ)^n*(1:ℂ)^(n*(n+1)))) *
      ∏ j ∈ Finset.range n, ((1:ℂ)-(1:ℂ)^(j+1)) := by
  norm_num [Finset.sum_range_succ, Finset.prod_range_succ, pochhammer]

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
      `EichlerEndpointFTC, `EichlerPathLimits, `EichlerBridge, `Order34QuantumPackets,
      `FORRadialProducts, `FORCyclotomicBlock, `FORPhiRadial, `FineRank, `FORGaussFinite,
      `FORRadialIdentity, `FORPhiProduct, `FORRankProduct, `FORGaussLimit, `FOROrder34,
      `ShadowReadings, `ShadowParity, `FranklinRows, `ShadowPentagonal, `ShadowHecke,
      `ShadowReconstruction, `ShadowPeriod, `GaussianEndpoint, `ShadowEndpoint,
      `ShadowEndpointValue24, `FORPsiRadial, `FOROrder24, `FORWatsonTerms, `FKTYReflection,
      `FORFiniteTransform, `FORWatsonBoundary, `FORWatsonQuotient, `FOREvenRoot, `FORWatsonCongruence,
      `FORWatsonMultiplicity]
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
      ``MockThetaAnalytic.fPackets34_tendsto_order10_period_of_FOR,
      ``MockThetaAnalytic.watsonPhi_head34,
      ``MockThetaAnalytic.radialEulerProduct,
      ``MockThetaAnalytic.radialPlusProduct,
      ``MockThetaAnalytic.hasProd_radialPochhammers,
      ``MockThetaAnalytic.radialPochhammers_ne_zero,
      ``MockThetaAnalytic.exists_radialPlus_prefix_bounds,
      ``MockThetaAnalytic.exists_radialPlus_interval_bounds,
      ``MockThetaAnalytic.exists_radialPlus_shift_lower,
      ``MockThetaAnalytic.radialEuler_mul_plus,
      ``MockThetaAnalytic.hasProd_radialB,
      ``MockThetaAnalytic.radialB_eq_pochhammers,
      ``MockThetaAnalytic.radialB_ne_zero,
      ``MockThetaAnalytic.order34_even_block,
      ``MockThetaAnalytic.watsonPhiTerm,
      ``MockThetaAnalytic.watsonPhi,
      ``MockThetaAnalytic.watsonPhiTerm_succ,
      ``MockThetaAnalytic.norm_watsonPhiTerm_radial_le,
      ``MockThetaAnalytic.watsonPhiTerm_add_seventeen,
      ``MockThetaAnalytic.summable_norm_watsonPhiTerm,
      ``MockThetaAnalytic.watsonPhi_eq_two_mul_sum,
      ``MockThetaAnalytic.watsonPhi_radial_limit,
      ``MockThetaAnalytic.summable_rankFine,
      ``MockThetaAnalytic.radialF_eq_two_sub_fine,
      ``MockThetaAnalytic.gaussEuler,
      ``MockThetaAnalytic.gaussWeight,
      ``MockThetaAnalytic.gaussEuler_ne_zero,
      ``MockThetaAnalytic.gauss_finite,
      ``MockThetaAnalytic.watsonOddTail,
      ``MockThetaAnalytic.watsonEvenTail,
      ``MockThetaAnalytic.watsonA,
      ``MockThetaAnalytic.watsonThetaHalf,
      ``MockThetaAnalytic.watsonOddTail_hasProd,
      ``MockThetaAnalytic.watsonEvenTail_hasProd,
      ``MockThetaAnalytic.watsonA_hasSum,
      ``MockThetaAnalytic.watson_least_part_split,
      ``MockThetaAnalytic.watsonThetaHalf_hasSum,
      ``MockThetaAnalytic.watson_weighted_phi_eq_theta_add_leastOdd,
      ``MockThetaAnalytic.radialPlus_mul_watsonPhi,
      ``MockThetaAnalytic.radialPlus_mul_radialF,
      ``MockThetaAnalytic.radialPlus_mul_radialB_eq_gauss,
      ``MockThetaAnalytic.radialPlus_mul_radialB_eq_thetaHalf,
      ``MockThetaAnalytic.watson_compensated_identity,
      ``MockThetaAnalytic.radialF_add_radialB_tendsto_order34,
      ``MockThetaAnalytic.fPackets34_tendsto_order10_period_unconditional,
      ``MockThetaAnalytic.ShadowReadings.observe_add_lifts,
      ``MockThetaAnalytic.ShadowReadings.reciprocal_fiber_constant,
      ``MockThetaAnalytic.ShadowReadings.shadow_fiber_constant,
      ``MockThetaAnalytic.ShadowParity.reciprocal_euler,
      ``MockThetaAnalytic.Franklin.flip_involution,
      ``MockThetaAnalytic.ShadowPentagonal.reciprocal_mock_pentagonal,
      ``MockThetaAnalytic.ShadowHecke.hecke_moment,
      ``MockThetaAnalytic.ShadowHecke.crank_integer_basis,
      ``MockThetaAnalytic.ShadowHecke.crank_basis_transport,
      ``MockThetaAnalytic.ShadowHecke.size_three_fixed_mask_fails,
      ``MockThetaAnalytic.ShadowReconstruction.mock_shadowMode_eq_cutoff,
      ``MockThetaAnalytic.ShadowReconstruction.mock_reconstruct_xiHalf_uniform,
      ``MockThetaAnalytic.ShadowReconstruction.mock_hecke_prefix,
      ``MockThetaAnalytic.ShadowReconstruction.mock_hecke_uniform,
      ``MockThetaAnalytic.ShadowPeriod.phase_add_144_changes_sector,
      ``MockThetaAnalytic.ShadowPeriod.weightedPhase_add_1584,
      ``MockThetaAnalytic.ShadowPeriod.recoveredPeriod_error,
      ``MockThetaAnalytic.ShadowPeriod.recoveredFullPeriod_error,
      ``MockThetaAnalytic.ShadowPeriod.recoveredTheta_sector,
      ``MockThetaAnalytic.ShadowPeriod.weightedCuspTheta_sector_eq_xiHalf,
      ``MockThetaAnalytic.ShadowPeriod.recoveredPeriod_uniform,
      ``MockThetaAnalytic.ShadowPeriod.recoveredPeriod_tendsto_normalizedPacketDefect,
      ``MockThetaAnalytic.ShadowPeriod.recoveredBoundary34_tendsto,
      ``MockThetaAnalytic.ShadowPeriod.recoveredTranslatedBoundary34,
      ``MockThetaAnalytic.ShadowPeriod.recoveredTranslatedBoundary34_error,
      ``MockThetaAnalytic.ShadowPeriod.boundary34Degree,
      ``MockThetaAnalytic.ShadowPeriod.recoveredTranslatedBoundary34_precision,
      ``MockThetaAnalytic.ShadowPeriod.boundary34ToleranceDegree,
      ``MockThetaAnalytic.ShadowPeriod.recoveredTranslatedBoundary34_tolerance,
      ``MockThetaAnalytic.integral_rootedGaussian,
      ``MockThetaAnalytic.integral_rootedGaussian_second_sub_le,
      ``MockThetaAnalytic.ShadowEndpoint.integrableOn_weightedCuspPeriod,
      ``MockThetaAnalytic.ShadowEndpoint.averagedFullPeriod_error,
      ``MockThetaAnalytic.ShadowEndpoint.averagedPeriod_uniform,
      ``MockThetaAnalytic.ShadowEndpoint.averagedFullPeriod_uniform,
      ``MockThetaAnalytic.ShadowEndpoint.rawFullPeriod_cusp_no_limit,
      ``MockThetaAnalytic.ShadowEndpoint.weightedCuspPeriod_cusp,
      ``MockThetaAnalytic.ShadowEndpoint.fktyCuspPeriod_eq_fktyPhi24,
      ``MockThetaAnalytic.ShadowEndpoint.averagedFullPeriod_eq_fktyPhi24,
      ``MockThetaAnalytic.watson_odd_product_series,
      ``MockThetaAnalytic.watson_compensated_sub_identity,
      ``MockThetaAnalytic.order24_odd_block, ``MockThetaAnalytic.watsonPsi_radial_limit24,
      ``MockThetaAnalytic.watsonPsi_head24, ``MockThetaAnalytic.fktyPhi_neg_one_div_24,
      ``MockThetaAnalytic.radialF_sub_radialB_tendsto_order24,
      ``MockThetaAnalytic.Order24Source.least_order24_packet_period,
      ``MockThetaAnalytic.Order24Source.smaller_anchor_loses_target,
      ``MockThetaAnalytic.Order24Source.source_winding4, ``MockThetaAnalytic.Order24Source.no_mod4_phase24,
      ``MockThetaAnalytic.Order24Source.translatedPacket24_eq_boundary,
      ``MockThetaAnalytic.Order24Source.translatedFPacketAtRadius24_eq,
      ``MockThetaAnalytic.Order24Source.normalizedPacket24_eq_averaged,
      ``MockThetaAnalytic.fPackets24_tendsto_boundary, ``MockThetaAnalytic.normalized_fPackets24_tendsto_averaged,
      ``MockThetaAnalytic.primitive_even_half_power, ``MockThetaAnalytic.watson_denominator_block,
      ``MockThetaAnalytic.norm_watsonTerm_radial_le, ``MockThetaAnalytic.watsonTerm_radial_limit,
      ``MockThetaAnalytic.watsonPhi_radial_limit_of_odd, ``MockThetaAnalytic.watsonPsi_radial_limit_of_even,
      ``MockThetaAnalytic.fNegPartial_reflection, ``MockThetaAnalytic.fktyPhi_reflected_boundary,
      ``MockThetaAnalytic.watsonFiniteBoundary_eq_of_certificate,
      ``MockThetaAnalytic.watson_factor_ne_zero_of_half_power, ``MockThetaAnalytic.watsonTerm_geometric,
      ``MockThetaAnalytic.watsonBoundaryCertificate_iff_cleared_zero,
      ``MockThetaAnalytic.even_root_order_of_half_power, ``MockThetaAnalytic.watson_denominator_blocks,
      ``MockThetaAnalytic.watson_cleared_identity, ``MockThetaAnalytic.watsonBoundaryCertificate_all,
      ``MockThetaAnalytic.polynomial_eq_zero_of_half_power_roots, ``MockThetaAnalytic.X_pow_add_one_dvd_iff_complex_roots,
      ``MockThetaAnalytic.watsonBoundaryCertificate_iff_polynomial_dvd, ``MockThetaAnalytic.watson_polynomial_congruence,
      ``MockThetaAnalytic.watson_even_polynomial_congruence,
      ``MockThetaAnalytic.watson_congruence, ``MockThetaAnalytic.watson_cleared_eq_of_half_power,
      ``MockThetaAnalytic.watson_congruence_prime_power,
      ``MockThetaAnalytic.map_watsonCongruenceDifference, ``MockThetaAnalytic.watsonQuotient,
      ``MockThetaAnalytic.watson_quotient_spec, ``MockThetaAnalytic.watson_derivative_at_neg_one,
      ``MockThetaAnalytic.watson_quotient_at_neg_one, ``MockThetaAnalytic.watson_extra_linear_factor_iff,
      ``MockThetaAnalytic.watson_quotient_derivative_at_neg_one,
      ``MockThetaAnalytic.watson_second_derivative_at_neg_one,
      ``MockThetaAnalytic.watson_derivative_at_neg_one_of_even, ``MockThetaAnalytic.watson_even_quotient_at_neg_one,
      ``MockThetaAnalytic.watson_rootMultiplicity_one_of_nonzero_slope,
      ``MockThetaAnalytic.watson_rootMultiplicity_odd_prime,
      ``MockThetaAnalytic.watson_rootMultiplicity_two_of_cast_eq_neg_one,
      ``MockThetaAnalytic.watson_rootMultiplicity_at_neg_one_of_odd,
      ``MockThetaAnalytic.watson_rootMultiplicity_at_neg_one_of_even,
      ``MockThetaAnalytic.watson_rootMultiplicity_at_neg_one,
      ``MockThetaAnalytic.radialF_compensated_tendsto_boundary_of_half_power,
      ``MockThetaAnalytic.radialF_compensated_tendsto_watson,
      ``MockThetaAnalytic.coupled_phase_fiber_constant_iff, ``MockThetaAnalytic.order22_shadow_anchor,
      ``MockThetaAnalytic.fPackets_tendsto_boundary_from_anchors,
      ``MockThetaAnalytic.watsonBoundaryCertificate_through_seventeen,
      ``MockThetaAnalytic.radialF_compensated_tendsto_boundary_through_order34,
      ``MockThetaAnalytic.fPackets_tendsto_boundary_through_order34,
      ``MockThetaAnalytic.finite_root_transform, ``MockThetaAnalytic.watsonFiniteBoundary_eq_boundaryValue,
      ``MockThetaAnalytic.finite_root_transform_at, ``MockThetaAnalytic.watson_even_reversed_numerator,
      ``MockThetaAnalytic.watson_odd_progression_at_odd_half_period,
      ``MockThetaAnalytic.radialF_compensated_tendsto_boundary, ``MockThetaAnalytic.fPackets_tendsto_boundary,
      ``MockThetaAnalytic.fPackets_tendsto_boundary_from_coupled_anchors,
      ``MockThetaAnalytic.normalized_fPackets_tendsto_fkty]
  unless required.all audited.contains do throwError "required public result missing from the audit"
  logInfo m!"PASS analytic audit: {audited.size} declarations in {modules.size} modules"
