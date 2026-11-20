import ShadowBounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Convex

/-! Absolute convergence and real differentiation of the full complementary-error-function
correction to Ramanujan’s integer-scaled third-order mock theta function. -/

noncomputable section

namespace MockThetaAnalytic

open Complex KElimination.MockThetaShadow KElimination.ShadowConvergence

/-- The full nonholomorphic correction, indexed by the absolute Fourier label. -/
def nonholomorphicPart (z : ℂ) : ℂ :=
  ∑' m : ℕ, nonholomorphicMode (shadowSign m : ℝ) m z

theorem summable_nonholomorphicModes (z : ℂ) (hz : 0 < z.im) :
    Summable fun m : ℕ => nonholomorphicMode (shadowSign m : ℝ) m z :=
  .of_norm_bounded (modeMajorant_summable z.im hz)
    (fun m => norm_signedMode_le m z.im hz z le_rfl)

/-- On the open half-plane above half the height of z, the same summable majorant
bounds every real derivative. This permits differentiating the series at z. -/
theorem hasFDerivAt_nonholomorphicPart (z : ℂ) (hz : 0 < z.im) :
    HasFDerivAt nonholomorphicPart
      (∑' m : ℕ, fderiv ℝ (nonholomorphicMode (shadowSign m : ℝ) m) z) z := by
  let a := z.im / 2
  have ha : 0 < a := half_pos hz
  have haz : a < z.im := half_lt_self hz
  apply hasFDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (s := {w : ℂ | a < w.im}) (x₀ := z)
    (modeMajorant_summable a ha) (isOpen_lt continuous_const Complex.continuous_im)
    (convex_halfSpace_im_gt a).isPreconnected
  · intro m w hw
    exact (differentiableAt_signedMode m w (ha.trans hw)).hasFDerivAt
  · intro m w hw
    exact norm_fderiv_signedMode_le m a ha w hw.le
  · exact haz
  · exact summable_nonholomorphicModes z hz
  · exact haz

theorem differentiableAt_nonholomorphicPart (z : ℂ) (hz : 0 < z.im) :
    DifferentiableAt ℝ nonholomorphicPart z :=
  (hasFDerivAt_nonholomorphicPart z hz).differentiableAt

/-- Evaluate the weight-one-half ξ operator on a real-linear derivative at fixed height. -/
private def xiDerivative (z : ℂ) : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2 * I * (Real.sqrt z.im : ℂ)) • (conjCLE.toContinuousLinearMap.comp
    ((2 : ℂ)⁻¹ • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) + I • ContinuousLinearMap.apply ℝ ℂ I)))

private theorem xiDerivative_fderiv (z : ℂ) (f : ℂ → ℂ) :
    xiDerivative z (fderiv ℝ f z) = xiHalf f z := by
  change _ * (starRingEnd ℂ) ((2 : ℂ)⁻¹ * _) = _ * (starRingEnd ℂ) (_ / 2)
  rw [div_eq_mul_inv, mul_comm (2 : ℂ)⁻¹]
  rfl

private theorem xiHalf_signedMode (m : ℕ) (z : ℂ) (hz : 0 < z.im) :
    xiHalf (nonholomorphicMode (shadowSign m : ℝ) m) z = 4 * shadowTerm (integerNome z) m := by
  cases m with
  | zero =>
    have h : nonholomorphicMode (shadowSign 0 : ℝ) (0 : ℝ) = fun _ => 0 := by
      funext w
      simp [nonholomorphicMode, modeAmplitude, shadowSign]
    simp [h, xiHalf, shadowTerm, shadowWeight]
  | succ m =>
    rw [xiHalf_nonholomorphicMode _ _ (by positivity) z hz]
    unfold shadowTerm integerNome shadowWeight
    rw [← Complex.exp_nat_mul, ← mul_assoc]
    congr 1
    · push_cast
      ring
    · congr 1
      push_cast
      ring

/-- The weight-one-half ξ derivative of the infinite correction equals four times
the convergent signed unary theta series in the integer-exponent nome. -/
theorem xiHalf_nonholomorphicPart (z : ℂ) (hz : 0 < z.im) :
    xiHalf nonholomorphicPart z = 4 * shadowSeries (integerNome z) := by
  have hs : Summable fun m : ℕ => fderiv ℝ (nonholomorphicMode (shadowSign m : ℝ) m) z :=
    .of_norm_bounded (modeMajorant_summable z.im hz)
      (fun m => norm_fderiv_signedMode_le m z.im hz z le_rfl)
  calc
    xiHalf nonholomorphicPart z = xiDerivative z (fderiv ℝ nonholomorphicPart z) :=
      (xiDerivative_fderiv z nonholomorphicPart).symm
    _ = ∑' m : ℕ, xiDerivative z (fderiv ℝ (nonholomorphicMode (shadowSign m : ℝ) m) z) := by
      rw [(hasFDerivAt_nonholomorphicPart z hz).fderiv, (xiDerivative z).map_tsum hs]
    _ = ∑' m : ℕ, 4 * shadowTerm (integerNome z) m := by
      apply tsum_congr
      intro m
      rw [xiDerivative_fderiv, xiHalf_signedMode m z hz]
    _ = 4 * shadowSeries (integerNome z) :=
      (shadowTerm_summable _ (norm_integerNome_lt_one z hz)).tsum_mul_left 4

end MockThetaAnalytic
