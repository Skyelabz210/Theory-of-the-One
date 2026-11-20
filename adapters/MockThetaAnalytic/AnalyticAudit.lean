import QuantumStrange
import QuantumRadialLimit
import MockCompletion
import BoundaryObservation34
import BoundaryValues34
import FKTYTheta
import QuantumTransport34
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

end

run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`ShadowConvergence, `ShadowOperator, `ShadowProjection, `ShadowMode,
      `QuantumRadialLimit, `QuantumStrange, `ShadowGaussian, `ShadowBounds, `ShadowInfinite,
      `MockHolomorphic, `ShadowSectors, `MockCompletion, `BoundaryObservation34,
      `BoundaryValues34, `FKTYTheta, `QuantumTransport34]
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
      ``MockThetaAnalytic.fPackets34_tendsto_order10_period]
  unless required.all audited.contains do throwError "required public result missing from the audit"
  logInfo m!"PASS analytic audit: {audited.size} declarations in {modules.size} modules"
