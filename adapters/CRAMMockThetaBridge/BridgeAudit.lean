import MockThetaAdapter
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Audit the declarations in the two imported adapter modules, including compiler-generated
helpers. `collectAxioms` follows types and proof bodies through the pinned upstream imports. -/

open Lean Elab Command CRAMMockThetaBridge

run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let required := #[``nat_dvd_mul_iff_period_dvd, ``int_dvd_mul_iff_period_dvd,
    ``fiber_constant_of_period_dvd, ``ReadoutCertificate,
    ``gcd_eq_one_of_inverse, ``singleton_resolution_of_inverse, ``target_fiber_constant_of_inverse,
    ``readout_and_target, ``finite_evaluation_from_nine65_anchor, ``finite_evaluation_from_nine65_adjacent,
    ``mockTheta_from_nine65_adjacent, ``phi_from_nine65_adjacent, ``psi_from_nine65_adjacent, ``chi_from_nine65_adjacent]
  let mut audited := #[]
  for mod in #[`BridgeArithmetic, `MockThetaAdapter] do
    let some idx := env.getModuleIdx? mod | throwError "missing module {mod}"
    let decls := env.header.moduleData[idx]!.constants
    if decls.isEmpty then throwError "empty module {mod}"
    for decl in decls do
      if let .thmInfo thm := decl then
        let isTrivial ← liftTermElabM <| Meta.forallTelescopeReducing thm.type fun _ body => do
          return (← Meta.whnf body).isConstOf ``True
        if isTrivial then throwError "theorem {decl.name} concludes True"
      let axioms ← collectAxioms decl.name
      if decl.isUnsafe || decl.isPartial || axioms.any (!allowed.contains ·) then
        throwError "unverified declaration {decl.name}, axioms {axioms}"
      audited := audited.push decl.name
      if required.contains decl.name then
        let deps := String.intercalate "," (axioms.toList.map toString).mergeSort
        logInfo m!"AUDIT {decl.name} [{deps}]"
  unless required.all audited.contains do throwError "missing required adapter declarations"
  logInfo m!"PASS bridge audit: {audited.size} kernel declarations, {required.size} required declarations"
