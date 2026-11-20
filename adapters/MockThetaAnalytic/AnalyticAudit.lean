import QuantumStrange
import QuantumRadialLimit
import MockCompletion
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

run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`ShadowConvergence, `ShadowOperator, `ShadowProjection, `ShadowMode,
      `QuantumRadialLimit, `QuantumStrange, `ShadowGaussian, `ShadowBounds, `ShadowInfinite,
      `MockHolomorphic, `ShadowSectors, `MockCompletion]
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
      ``MockThetaAnalytic.xiHalf_project11_mockCompletion_eq_zero_iff]
  unless required.all audited.contains do throwError "required public result missing from the audit"
  logInfo m!"PASS analytic audit: {audited.size} declarations in {modules.size} modules"
