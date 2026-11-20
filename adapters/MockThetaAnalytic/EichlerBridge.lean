import EichlerPrimitive
import EichlerEndpointFTC
import EichlerPathLimits
import EichlerBoundaryValues
import FKTYThetaTransform

/-! The FKTY weight-half quantum transformation at the two reflected cusps.
A single primitive compares the straight rays and the inverse image of the
order-10 ray. The finite cusp moments supply its boundary differences. -/

noncomputable section
namespace MockThetaAnalytic
open Complex MeasureTheory Set Filter KElimination.QuantumRadial
open scoped Topology

/-- The normalized weight-half defect at −1/34 equals the actual Eichler
period from −1/24 to i∞, with the principal square root. -/
theorem fkty_defect34_eq_period :
    fktyPhi (-1/34) - (Real.sqrt (17/5) : ℂ) * fktyPhi (-1/10) =
      fktyVerticalPeriod fktyTheta (-1/24) (-1/34) := by
  let x : ℝ := -1/34
  let s : ℝ := -1/24
  let v (c t : ℝ) : ℂ := (c : ℂ) + (t : ℂ)*I
  let P := fktyVerticalPeriod fktyTheta (-1/24) (-1/34)
  let w : ℂ := Real.sqrt (17/5)
  obtain ⟨F, hd⟩ := exists_eichlerPrimitive x
  have hF : ∀ z : ℂ, 0 < z.im →
      HasDerivAt F (fktyTheta z / ((z-(-1/34))^(1/2:ℂ))) z := by
    simpa [eichlerForm, x] using hd
  let pole (t : ℝ) := I * fktyTheta (v s t) / ((v s t-(-1/34))^(1/2:ℂ))
  have hp : IntegrableOn pole (Ioi 0) := by simpa [pole, v, s] using integrableOn_fktyPeriod34
  have hval : (∫ t in Ioi (0:ℝ), pole t) = P := by
    simp [pole, v, s, P, fktyVerticalPeriod]
  obtain ⟨T, htop, hbot⟩ := primitive_ray_endpoints (fun t => F (v s t)) pole hp
    (fun t ht => by simpa [pole, v, s, x, eichlerForm, mul_div_assoc] using
      hasDerivAt_eichlerPrimitive_vertical x s t ht F hd)
  rw [hval] at hbot
  have topX : Tendsto (fun t => F (v x t)) atTop (𝓝 T) := by
    have h := (eichlerPrimitive_vertical_gap_top x s x F hd).add htop
    simpa [v] using h
  have nearX : Tendsto (fun t => F (v x t)) (𝓝[>] 0) (𝓝 (T - fktyPhi (-1/34))) := by
    apply ((tendsto_const_nhds (x := T)).sub fktyEichler_boundaryLimits34.2).congr'
    filter_upwards [self_mem_nhdsWithin] with b hb
    have hb' : 0 < b := hb
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := b)
      (f := fun t => F (v x t)) (f' := fktyEichlerIntegrand x 0)
      (fun t ht => by simpa [v, fktyEichlerIntegrand, eichlerForm, mul_div_assoc] using
        hasDerivAt_eichlerPrimitive_vertical x x t (lt_of_lt_of_le hb' ht) F hd)
      (integrableOn_fktyEichlerTrunc x b 0 hb' le_rfl) topX
    change T - (∫ t in Ioi b, fktyEichlerIntegrand x 0 t) = _
    rw [h]
    abel
  let arc (t : ℝ) := F (eichlerInverseRay t)
  have arcTop : Tendsto arc atTop (𝓝 (T-P)) := by
    have hu := (eichlerPrimitive_inverseRay_gap_infty F hF).add
      (hbot.comp eichlerInverseRay_height_infty)
    simpa [Function.comp_def, arc, v, s] using hu
  have arcBot : Tendsto arc (𝓝[>] 0) (𝓝 (T - fktyPhi (-1/34))) := by
    have hu := (eichlerPrimitive_inverseRay_gap_zero F hF).add
      (nearX.comp eichlerInverseRay_height_zero)
    simpa [Function.comp_def, arc, v, x] using hu
  have heq : ∀ᶠ b in 𝓝[>] (0:ℝ), w * fktyEichlerTrunc (-1/10) b 0 = (T-P) - arc b := by
    filter_upwards [self_mem_nhdsWithin] with b hb
    have hb' : 0 < b := hb
    have hi := (integrableOn_fktyEichlerTrunc (-1/10) b 0 hb' le_rfl).const_mul w
    rw [fktyEichlerTrunc, ← integral_const_mul]
    apply integral_Ioi_of_hasDerivAt_of_tendsto' _ hi arcTop
    intro t ht
    have ht' := lt_of_lt_of_le hb' ht
    have hm := fktyTheta_lower_unipotent _ (eichlerInverseRay_im_pos t ht')
    simpa [w, arc, fktyEichlerIntegrand, eichlerTargetRay] using
      hasDerivAt_eichlerPrimitive_inverseRay F hF t ht' hm
  have left := ((tendsto_const_nhds (x := w)).mul fktyEichler_boundaryLimits10.2).congr' heq
  have right := (tendsto_const_nhds (x := T-P)).sub arcBot
  have eq := tendsto_nhds_unique left right
  change fktyPhi (-1/34) - w * fktyPhi (-1/10) = P
  linear_combination -eq

end MockThetaAnalytic
