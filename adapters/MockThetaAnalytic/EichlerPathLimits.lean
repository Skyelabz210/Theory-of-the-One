import EichlerTransportPath
import EichlerHorizontal

/-! Vanishing horizontal pieces used to deform the Eichler contour.
Near either end of the Möbius arc the horizontal displacement is quadratic
in the height. At the upper end of two vertical paths it is constant. -/
noncomputable section
namespace MockThetaAnalytic
open Complex Filter Set
open scoped Topology

/-- Vertical paths above any two fixed real points have the same limiting
primitive value at infinity whenever one of the limits exists. -/
theorem eichlerPrimitive_vertical_gap_top (x c c' : ℝ) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im →
      HasDerivAt F (fktyTheta z / ((z-(x:ℂ))^(1/2:ℂ))) z) :
    Tendsto (fun t : ℝ => F ((c':ℂ)+(t:ℂ)*I) - F ((c:ℂ)+(t:ℂ)*I)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun t : ℝ => ((24/Real.pi)*|c'-c|) / t)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have h := norm_horizontal_bridge_le x c c' t (by linarith) F hF
    exact h.trans (div_le_div_of_nonneg_left (by positivity) (by linarith)
      (le_mul_of_one_le_right (by linarith) (Real.one_le_sqrt.mpr ht)))
  · exact tendsto_const_nhds.div_atTop tendsto_id

private theorem primitive_gap_of_quadratic_offset {α : Type*} {l : Filter α}
    (x c C : ℝ) (z : α → ℂ) (F : ℂ → ℂ)
    (hF : ∀ w : ℂ, 0 < w.im →
      HasDerivAt F (fktyTheta w / ((w-(x:ℂ))^(1/2:ℂ))) w)
    (hheight : Tendsto (fun t => (z t).im) l (𝓝[>] 0))
    (hoff : ∀ᶠ t in l, |(z t).re-c| ≤ C*(z t).im^2) :
    Tendsto (fun t => F (z t) - F ((c:ℂ)+((z t).im:ℂ)*I)) l (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun t => (24/Real.pi)*C*Real.sqrt (z t).im)
  · filter_upwards [hoff, hheight.eventually self_mem_nhdsWithin] with t ht hpos
    have hpos' : 0 < (z t).im := hpos
    have h := norm_horizontal_bridge_le x c (z t).re (z t).im hpos' F hF
    rw [Complex.re_add_im] at h
    refine h.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 24 / Real.pi))
      (by positivity)).trans_eq ?_)
    have hsq := Real.sq_sqrt hpos'.le
    have hs := Real.sqrt_pos.mpr hpos'
    field_simp
    rw [hsq]
  · simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_nhdsWithin_iff.mp hheight).1).const_mul ((24/Real.pi)*C)

/-- At the lower end of the target ray, its preimage has the vertical
boundary value at −1/34. -/
theorem eichlerPrimitive_inverseRay_gap_zero (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im →
      HasDerivAt F (fktyTheta z / ((z-(-1/34))^(1/2:ℂ))) z) :
    Tendsto (fun t => F (eichlerInverseRay t) -
      F ((-1/34:ℂ)+((eichlerInverseRay t).im:ℂ)*I)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  simpa only [ofReal_neg, ofReal_one, ofReal_div, ofReal_ofNat] using
    primitive_gap_of_quadratic_offset (-1/34) (-1/34) 5000 eichlerInverseRay F
      (by simpa using hF) eichlerInverseRay_height_zero eichlerInverseRay_offset_zero

/-- At the upper end of the target ray, its preimage has the vertical
boundary value at the pole −1/24. -/
theorem eichlerPrimitive_inverseRay_gap_infty (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im →
      HasDerivAt F (fktyTheta z / ((z-(-1/34))^(1/2:ℂ))) z) :
    Tendsto (fun t => F (eichlerInverseRay t) -
      F ((-1/24:ℂ)+((eichlerInverseRay t).im:ℂ)*I)) atTop (𝓝 0) := by
  simpa only [ofReal_neg, ofReal_one, ofReal_div, ofReal_ofNat] using
    primitive_gap_of_quadratic_offset (-1/34) (-1/24) 100 eichlerInverseRay F
      (by simpa using hF) eichlerInverseRay_height_infty eichlerInverseRay_offset_infty

end MockThetaAnalytic
