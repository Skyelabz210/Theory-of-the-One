import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.PSeries

/-! Absolute integrability of differences of Gaussian Fourier modes on the positive
height ray. The shift cancels the nonsummable first-order term in their integrals. -/

noncomputable section

namespace MockThetaAnalytic

open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- A positive-frequency Gaussian mode, with height as its last argument. -/
def gaussianMode (a : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  (m : ℝ) * Real.exp (-(a * (m : ℝ)^2) * t)

theorem integrableOn_gaussianMode (a : ℝ) (ha : 0 < a) (m : ℕ) :
    IntegrableOn (gaussianMode a m) (Ioi 0) := by
  cases m with
  | zero =>
    unfold gaussianMode
    simp [IntegrableOn]
  | succ m =>
    exact (integrableOn_exp_mul_Ioi (a := -(a * ((m+1 : ℕ) : ℝ)^2))
      (neg_lt_zero.mpr (by positivity)) 0).const_mul _

/-- Pairing frequencies a fixed distance apart makes their absolute difference
integrable with a summable bound in the starting frequency. -/
theorem integral_norm_gaussianMode_sub_le (a : ℝ) (ha : 0 < a) (m D : ℕ) (hm : 0 < m) :
    (∫ t : ℝ in Ioi 0, ‖gaussianMode a m t - gaussianMode a (m+D) t‖) ≤
      3 * D / (a * (m : ℝ)^2) := by
  let x : ℝ := m
  let d : ℝ := D
  let y : ℝ := x + d
  have hx : 0 < x := by dsimp [x]; exact_mod_cast hm
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hxy : x ≤ y := by dsimp [y]; linarith
  have hy : 0 < y := hx.trans_le hxy
  let E (z t : ℝ) := Real.exp (-(a*z^2)*t)
  have hE (z : ℝ) (hz : 0 < z) : IntegrableOn (E z) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (mul_pos ha (sq_pos_of_pos hz))) 0
  have valE (z : ℝ) (hz : 0 < z) : (∫ t : ℝ in Ioi 0, E z t) = 1/(a*z^2) := by
    dsimp [E]
    rw [integral_exp_mul_Ioi (neg_lt_zero.mpr (mul_pos ha (sq_pos_of_pos hz)))]
    simp
  have hmajor := (((hE x hx).sub (hE y hy)).const_mul x).add ((hE y hy).const_mul d)
  have hbound (t : ℝ) (ht : 0 < t) :
      ‖gaussianMode a m t - gaussianMode a (m+D) t‖ ≤ x*(E x t-E y t)+d*E y t := by
    have hmono : E y t ≤ E x t := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hx.le hxy 2) ha.le)) ht.le
    have h₁ : 0 ≤ x*(E x t-E y t) := mul_nonneg hx.le (sub_nonneg.mpr hmono)
    have h₂ : 0 ≤ d*E y t := mul_nonneg hd (Real.exp_pos _).le
    have heq : gaussianMode a m t - gaussianMode a (m+D) t =
        x*(E x t-E y t)-d*E y t := by
      simp only [gaussianMode, Nat.cast_add, x, d, y, E]; ring
    rw [heq, Real.norm_eq_abs]
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have habs := ((integrableOn_gaussianMode a ha m).sub (integrableOn_gaussianMode a ha (m+D))).norm
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, (x*(E x t-E y t)+d*E y t) :=
      integral_mono_ae habs hmajor ((ae_restrict_mem measurableSet_Ioi).mono hbound)
    _ = x*(1/(a*x^2)-1/(a*y^2))+d*(1/(a*y^2)) := by
      have hi : IntegrableOn (fun t => E x t - E y t) (Ioi 0) := (hE x hx).sub (hE y hy)
      rw [integral_add (hi.const_mul x) ((hE y hy).const_mul d),
        integral_const_mul, integral_const_mul, integral_sub (hE x hx) (hE y hy), valE x hx, valE y hy]
    _ ≤ _ := by
      change _ ≤ 3*d/(a*x^2)
      field_simp
      dsimp [y]
      ring_nf
      nlinarith [mul_nonneg (sq_nonneg d) hx.le, mul_nonneg (sq_nonneg d) hd]

private theorem integrable_tsum_of_summable_integral_norm {μ : Measure ℝ} (F : ℕ → ℝ → ℂ)
    (hi : ∀ m, Integrable (F m) μ) (hs : Summable (fun m => ∫ t, ‖F m t‖ ∂μ)) :
    Integrable (fun t => ∑' m, F m t) μ := by
  have hm (m : ℕ) : AEMeasurable (fun t => ‖F m t‖ₑ) μ := (hi m).1.enorm
  have hfinite : (∫⁻ t, ∑' m, ‖F m t‖ₑ ∂μ) < ∞ := by
    rw [lintegral_tsum hm]
    simpa only [ofReal_integral_norm_eq_lintegral_enorm (hi _)] using hs.tsum_ofReal_lt_top
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum hm) hfinite.ne
  constructor
  · apply aestronglyMeasurable_of_tendsto_ae (f := fun n t => ∑ m ∈ Finset.range n, F m t) atTop
    · intro n
      exact (Finset.range n).aestronglyMeasurable_fun_sum (fun m _ => (hi m).1)
    · filter_upwards [hae] with t ht
      have habs : Summable (fun m => (‖F m t‖₊ : ℝ)) :=
        ENNReal.tsum_coe_ne_top_iff_summable_coe.mp ht.ne
      exact habs.of_norm.hasSum.tendsto_sum_nat
  · exact (lintegral_mono (fun t => enorm_tsum_le_tsum_enorm (f := fun m => F m t))).trans_lt hfinite

/-- Bounded complex phases may be retained when summing the paired modes in L¹. -/
theorem integrableOn_gaussianMode_pair_series (a : ℝ) (ha : 0 < a) (D : ℕ) (w : ℕ → ℂ)
    (hw : ∀ m, ‖w m‖ ≤ 1) :
    IntegrableOn (fun t => ∑' m, w m *
      ((gaussianMode a m t - gaussianMode a (m+D) t : ℝ) : ℂ)) (Ioi 0) := by
  let F (m : ℕ) (t : ℝ) := w m * ((gaussianMode a m t - gaussianMode a (m+D) t : ℝ) : ℂ)
  have hpair (m : ℕ) : IntegrableOn (fun t => gaussianMode a m t - gaussianMode a (m+D) t)
      (Ioi 0) := (integrableOn_gaussianMode a ha m).sub (integrableOn_gaussianMode a ha (m+D))
  have hi (m : ℕ) : IntegrableOn (F m) (Ioi 0) := (hpair m).ofReal.const_mul _
  apply integrable_tsum_of_summable_integral_norm F hi
  apply ((Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left (3*D/a : ℝ)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  rw [Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg _))]
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, ‖gaussianMode a m t - gaussianMode a (m+D) t‖ := by
      apply integral_mono (hi m).norm (hpair m).norm
      intro t
      simpa only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul] using
        mul_le_mul_of_nonneg_right (hw m) (abs_nonneg (gaussianMode a m t - gaussianMode a (m+D) t))
    _ ≤ _ := (integral_norm_gaussianMode_sub_le a ha m D hm).trans_eq (by ring)

end MockThetaAnalytic
