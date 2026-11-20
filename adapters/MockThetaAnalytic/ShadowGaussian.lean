import ShadowMode
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Gaussian tail estimates for the complementary error function used in
the nonholomorphic modes of the third-order mock theta completion. -/

noncomputable section

namespace MockThetaAnalytic

open MeasureTheory Set

private theorem gaussian_integrable :
    Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
  simpa using integrable_exp_neg_mul_sq (b := (1 : ℝ)) zero_lt_one

/-- Split the normalized half-line Gaussian integral at a nonnegative argument. -/
theorem erfc_eq_tail_integral (x : ℝ) (hx : 0 ≤ x) :
    erfc x = (2 / Real.sqrt Real.pi) * ∫ t in Ioi x, Real.exp (-(t ^ 2)) := by
  have htotal : (∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 2))) = Real.sqrt Real.pi / 2 := by
    simpa using integral_gaussian_Ioi 1
  have hsplit := setIntegral_union (f := fun t : ℝ => Real.exp (-(t ^ 2)))
    (Ioc_disjoint_Ioi_same (a := 0) (b := x)) measurableSet_Ioi
    gaussian_integrable.integrableOn gaussian_integrable.integrableOn
  rw [Ioc_union_Ioi_eq_Ioi hx, htotal] at hsplit
  rw [erfc, intervalIntegral.integral_of_le hx]
  field_simp [(Real.sqrt_pos.2 Real.pi_pos).ne']
  linarith

theorem erfc_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ erfc x := by
  rw [erfc_eq_tail_integral x hx]
  exact mul_nonneg (by positivity) (integral_nonneg fun t => (Real.exp_pos _).le)

/-- The tangent line to `-t²` at `x` bounds the Gaussian above by an
exponential whose tail integral can be evaluated explicitly. -/
theorem abs_erfc_le (x : ℝ) (hx : 0 < x) :
    |erfc x| ≤ Real.exp (-(x ^ 2)) / (Real.sqrt Real.pi * x) := by
  have hneg : -2 * x < 0 := by linarith
  have htail : (∫ t in Ioi x, Real.exp (-(t ^ 2))) ≤ Real.exp (-(x ^ 2)) / (2 * x) := calc
    _ ≤ ∫ t in Ioi x, Real.exp (x ^ 2) * Real.exp ((-2 * x) * t) := by
      apply setIntegral_mono_on gaussian_integrable.integrableOn
        ((integrableOn_exp_mul_Ioi hneg x).const_mul _) measurableSet_Ioi
      intro t _
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith [sq_nonneg (t - x)]
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi hneg,
        show -2 * x = -(2 * x) by ring, neg_div_neg_eq, ← mul_div_assoc, ← Real.exp_add]
      congr 2
      ring
  rw [abs_of_nonneg (erfc_nonneg x hx.le), erfc_eq_tail_integral x hx.le]
  calc
    _ ≤ (2 / Real.sqrt Real.pi) * (Real.exp (-(x ^ 2)) / (2 * x)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

end MockThetaAnalytic
