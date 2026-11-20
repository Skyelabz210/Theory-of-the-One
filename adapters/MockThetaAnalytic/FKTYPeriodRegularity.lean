import QuantumTransport34
import FKTYCuspModes
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Absolute integrability at the FKTY cusp −1/24 and real analyticity of the
resulting period away from that cusp, including the parameter −1/34. The proof
uses Gaussian cancellation and differentiation under the integral. -/
noncomputable section
namespace MockThetaAnalytic
open Complex MeasureTheory Set Filter
open scoped Topology

/-- The square-root factor in the vertical parameter, including du = i dt. -/
def fktyVerticalKernel (s x t : ℝ) : ℂ :=
  I / (((s : ℂ) + (t : ℂ) * I - (x : ℂ)) ^ (1 / 2 : ℂ))

/-- At a parameter distinct from the vertical line's real part, the
denominator stays uniformly away from zero, including at height zero. -/
theorem norm_fktyVerticalKernel_le (s x t : ℝ) (hx : s ≠ x) :
    ‖fktyVerticalKernel s x t‖ ≤ 1 / Real.sqrt |s - x| := by
  let z : ℂ := (s : ℂ) + (t : ℂ) * I - (x : ℂ)
  have hre : |s - x| ≤ ‖z‖ := by simpa [z] using abs_re_le_norm z
  have hp : (0 : ℝ) < Real.sqrt |s - x| := Real.sqrt_pos.2 (abs_pos.mpr (sub_ne_zero.mpr hx))
  have hnorm : ‖z ^ (1 / 2 : ℂ)‖ = Real.sqrt ‖z‖ := by
    simpa [Real.sqrt_eq_rpow] using norm_cpow_real z (1/2)
  change ‖I / (z ^ (1/2 : ℂ))‖ ≤ _
  rw [norm_div, norm_I, hnorm]
  exact one_div_le_one_div_of_le hp (Real.sqrt_le_sqrt hre)

/-- Above the real axis, the principal square root remains on its analytic branch. -/
theorem continuousOn_fktyVerticalKernel (s x : ℝ) :
    ContinuousOn (fktyVerticalKernel s x) (Ioi 0) := by
  let z (t : ℝ) : ℂ := (s : ℂ) + (t : ℂ) * I - (x : ℂ)
  have hcont : Continuous z := by dsimp [z]; fun_prop
  have hslit (t : ℝ) (ht : t ∈ Ioi 0) : z t ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    exact Or.inr (by simpa [z] using (ne_of_gt ht))
  apply continuousOn_const.div (hcont.continuousOn.cpow_const hslit)
  exact fun t ht => cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (hslit t ht)))

/-- Multiplying an integrable numerator by the FKTY square-root factor
preserves integrability on the full open vertical ray. -/
theorem integrableOn_fktyVerticalKernel_mul (s x : ℝ) (hx : s ≠ x) (g : ℝ → ℂ)
    (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun t => fktyVerticalKernel s x t * g t) (Ioi 0) :=
  hg.bdd_mul ((continuousOn_fktyVerticalKernel s x).aestronglyMeasurable measurableSet_Ioi)
    (Filter.Eventually.of_forall fun t => norm_fktyVerticalKernel_le s x t hx)

/-- Absolute integrability of the actual theta series on the whole cusp ray.
Antiperiodic cancellation is kept inside each Gaussian difference. -/
theorem integrableOn_fktyTheta_cusp :
    IntegrableOn (fun t : ℝ => fktyTheta ((-1/24 : ℂ) + (t : ℂ) * I)) (Ioi 0) := by
  have ha : 0 < Real.pi / 12 := by positivity
  have hhead : IntegrableOn (fun t : ℝ => ∑ m ∈ Finset.range 144,
      fktyCuspPhase m * (gaussianMode (Real.pi / 12) m t : ℂ)) (Ioi 0) :=
    integrable_finset_sum _ fun m _ => (integrableOn_gaussianMode _ ha m).ofReal.const_mul _
  have hpair := integrableOn_gaussianMode_pair_series (Real.pi / 12) ha 144
    fktyCuspPhase norm_fktyCuspPhase_le_one
  exact IntegrableOn.congr_fun (hhead.add hpair) (fun t ht => (fktyTheta_cusp_paired t ht).symm) measurableSet_Ioi

/-- The Bochner integral in the transport law at −1/34 is absolutely
convergent, independently of the period transformation law. -/
theorem integrableOn_fktyPeriod34 :
    IntegrableOn (fun t : ℝ => let u : ℂ := (-1/24 : ℂ) + (t : ℂ) * I
      I * fktyTheta u / ((u - (-1/34 : ℂ)) ^ (1 / 2 : ℂ))) (Ioi 0) := by
  have h := integrableOn_fktyVerticalKernel_mul (-1/24) (-1/34) (by norm_num) _
    integrableOn_fktyTheta_cusp
  apply h.congr_fun _ measurableSet_Ioi
  intro t _
  simp only [fktyVerticalKernel, ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat]
  ring

/-- The period with a real boundary parameter extends the rational definition
and varies continuously away from the cusp −1/24. -/
def fktyCuspPeriod (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), fktyVerticalKernel (-1/24) x t * fktyTheta ((-1/24 : ℂ) + (t : ℂ) * I)

theorem fktyCuspPeriod_rat (x : ℚ) :
    fktyCuspPeriod (x : ℝ) = fktyVerticalPeriod fktyTheta (-1/24) x := by
  unfold fktyCuspPeriod fktyVerticalPeriod
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp [fktyVerticalKernel]
  push_cast
  ring

/-- On the positive-height ray, rotation by π relates the two principal
square roots from above and gives the holomorphic continuation on the right. -/
theorem fktyVerticalKernel_eq_rotated (s x t : ℝ) (ht : 0 < t) :
    fktyVerticalKernel s x t =
      ((x : ℂ) - ((s : ℂ) + (t : ℂ) * I)) ^ (-(1/2) : ℂ) := by
  let v : ℂ := (x : ℂ) - ((s : ℂ) + (t : ℂ) * I)
  have him : v.im < 0 := by simpa [v] using (neg_lt_zero.mpr ht)
  have hv : v ≠ 0 := by intro he; simp [he] at him
  have hlog : log (-v) = log v + (Real.pi : ℂ) * I := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simpa [Complex.log_im] using arg_neg_eq_arg_add_pi_of_im_neg him
  have hphase : Complex.exp ((Real.pi : ℂ) * I * (1/2)) = I := by
    rw [show (Real.pi : ℂ) * I * (1/2) = (Real.pi : ℂ)/2 * I by ring, exp_pi_div_two_mul_I]
  have hroot : (-v) ^ (1/2 : ℂ) = v ^ (1/2 : ℂ) * I := by
    rw [cpow_def_of_ne_zero (neg_ne_zero.mpr hv), cpow_def_of_ne_zero hv,
      hlog, add_mul, exp_add, hphase]
  rw [fktyVerticalKernel, show (s : ℂ) + (t : ℂ)*I - (x : ℂ) = -v by dsimp [v]; ring,
    hroot, cpow_neg]
  change _ = (v ^ (1/2 : ℂ))⁻¹
  field_simp [I_ne_zero]

private def shiftedPower (s b p : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (z - ((s : ℂ) + ((b*t : ℝ) : ℂ)*I)) ^ (p : ℂ)

private theorem norm_shiftedPower_le {s b p d : ℝ} (hd : 0 < d) (hp : p ≤ 0)
    (z : ℂ) (hz : d ≤ z.re - s) (t : ℝ) : ‖shiftedPower s b p z t‖ ≤ d ^ p := by
  rw [shiftedPower, norm_cpow_real]
  apply Real.rpow_le_rpow_of_nonpos hd _ hp
  exact hz.trans (by simpa using re_le_norm (z - ((s : ℂ) + ((b*t : ℝ) : ℂ)*I)))

private theorem continuous_shiftedPower (s b p : ℝ) (z : ℂ) (hz : s < z.re) :
    Continuous (shiftedPower s b p z) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  unfold shiftedPower
  apply continuousAt_cpow_const _ |>.comp
  · fun_prop
  · exact mem_slitPlane_iff.mpr (Or.inl (by simpa using sub_pos.mpr hz))

/-- Differentiation under the period integral on a half-plane where the
translated base has positive real part. The imaginary part of the shift is b t. -/
private theorem differentiableAt_shiftedPeriod (s b : ℝ) (g : ℝ → ℂ)
    (hg : IntegrableOn g (Ioi 0)) (z : ℂ) (hz : s < z.re) :
    DifferentiableAt ℂ (fun w : ℂ => ∫ t in Ioi (0 : ℝ),
      shiftedPower s b (-(1/2)) w t * g t) z := by
  let p : ℝ := -(1/2)
  let d : ℝ := (z.re - s)/2
  have hd : 0 < d := half_pos (sub_pos.mpr hz)
  have hball {w : ℂ} (hw : w ∈ Metric.ball z d) : d ≤ w.re - s := by
    have hle : z.re - w.re ≤ ‖z - w‖ := by simpa using re_le_norm (z - w)
    have hh : z.re - w.re < d := hle.trans_lt (by rwa [← dist_eq_norm, dist_comm])
    dsimp [d] at *
    linarith
  let F (w : ℂ) (t : ℝ) := shiftedPower s b p w t * g t
  let F' (w : ℂ) (t : ℝ) := ((p : ℂ) * shiftedPower s b (p-1) w t) * g t
  have hint : IntegrableOn (F z) (Ioi 0) := hg.bdd_mul
    ((continuous_shiftedPower _ _ _ z hz).aestronglyMeasurable)
    (Eventually.of_forall fun t => norm_shiftedPower_le hd (by norm_num [p]) z (by dsimp [d]; linarith) t)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := z)
    (μ := volume.restrict (Ioi 0)) (bound := fun t => (‖(p : ℂ)‖ * d ^ (p-1)) * ‖g t‖) hd
    _ hint _ _ (hg.norm.const_mul _) _).2.differentiableAt
  · filter_upwards [Metric.ball_mem_nhds z hd] with w hw
    exact (continuous_shiftedPower _ _ _ w (by linarith [hball hw])).aestronglyMeasurable.mul
      hg.aestronglyMeasurable
  · exact ((continuous_const.mul (continuous_shiftedPower _ _ _ z hz)).aestronglyMeasurable).mul hg.aestronglyMeasurable
  · apply Eventually.of_forall
    intro t w hw
    dsimp [F']
    rw [norm_mul, norm_mul]
    gcongr
    exact norm_shiftedPower_le hd (by norm_num [p]) w (hball hw) t
  · apply Eventually.of_forall
    intro t w hw
    have hslit : w - ((s : ℂ) + ((b*t : ℝ) : ℂ)*I) ∈ slitPlane :=
      mem_slitPlane_iff.mpr <| Or.inl (by simpa using (hd.trans_le (hball hw)))
    have H := (((hasDerivAt_id w).sub_const ((s : ℂ) + ((b*t : ℝ) : ℂ)*I)).cpow_const
      (c := (p : ℂ)) hslit).mul_const (g t)
    simpa only [F, F', shiftedPower, Complex.ofReal_sub, Complex.ofReal_one,
      id_eq, mul_one] using H

private theorem analyticAt_shiftedPeriod_real (s b : ℝ) (g : ℝ → ℂ)
    (hg : IntegrableOn g (Ioi 0)) (x : ℝ) (hx : s < x) :
    AnalyticAt ℝ (fun y : ℝ => ∫ t in Ioi (0 : ℝ),
      shiftedPower s b (-(1/2)) y t * g t) x := by
  let f (z : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), shiftedPower s b (-(1/2)) z t * g t
  have hdiff : DifferentiableOn ℂ f {z : ℂ | s < z.re} :=
    fun z hz => (differentiableAt_shiftedPeriod s b g hg z hz).differentiableWithinAt
  have hN : {z : ℂ | s < z.re} ∈ 𝓝 (x : ℂ) := continuous_re.continuousAt (Ioi_mem_nhds hx)
  exact (hdiff.analyticAt hN).restrictScalars.comp (Complex.ofRealCLM.analyticAt x)

private def thetaRay (t : ℝ) : ℂ := fktyTheta ((-1/24 : ℂ) + (t : ℂ) * I)

private theorem period_rotated (x : ℝ) :
    fktyCuspPeriod x = ∫ t in Ioi (0 : ℝ), shiftedPower (-1/24) 1 (-(1/2)) x t * thetaRay t := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [fktyVerticalKernel_eq_rotated _ _ _ ht]
  simp [shiftedPower, thetaRay]

private theorem period_unrotated (x : ℝ) :
    fktyCuspPeriod x = I * ∫ t in Ioi (0 : ℝ),
      shiftedPower (1/24) (-1) (-(1/2)) (-x) t * thetaRay t := by
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only [fktyVerticalKernel, shiftedPower, thetaRay]
  push_cast
  simp only [cpow_neg, div_eq_mul_inv, one_mul, neg_mul]
  ring_nf

/-- At every real parameter other than the cusp, the period is real-analytic.
On each component the proof extends the integrand holomorphically to the
half-plane on the same side of the vertical line, then differentiates the
integral there using the integrable theta numerator. -/
theorem analyticAt_fktyCuspPeriod (x : ℝ) (hx : x ≠ -1/24) :
    AnalyticAt ℝ fktyCuspPeriod x := by
  by_cases hr : -1/24 < x
  · have H := analyticAt_shiftedPeriod_real (-1/24) 1 thetaRay integrableOn_fktyTheta_cusp x hr
    exact H.congr (Eventually.of_forall fun y => (period_rotated y).symm)
  · have hl : 1/24 < -x := by linarith [lt_of_le_of_ne (le_of_not_gt hr) hx]
    have H := analyticAt_shiftedPeriod_real (1/24) (-1) thetaRay integrableOn_fktyTheta_cusp (-x) hl
    have Hneg := H.comp (analyticAt_id (𝕜 := ℝ) (z := x)).neg
    apply (analyticAt_const (v := I) |>.mul Hneg).congr
    apply Eventually.of_forall
    intro y
    simpa only [Pi.mul_apply, Function.comp_apply, ofReal_neg] using (period_unrotated y).symm

theorem continuousAt_fktyCuspPeriod (x : ℝ) (hx : x ≠ -1/24) :
    ContinuousAt fktyCuspPeriod x :=
  (analyticAt_fktyCuspPeriod x hx).continuousAt

/-- On the right-hand component of the quantum set, the published FKTY
transformation identifies this real-analytic period with the same matrix's
defect for every reduced even-denominator cusp. -/
theorem fktyPhi_defect_eq_cuspPeriod (hFKTY : FKTYWeightHalfLaw) (x : ℚ)
    (he : Even x.den) (hx : -1/24 < x) :
    fktyPhi x - (((24*x+1 : ℚ) : ℂ) ^ (-1/2 : ℂ)) * fktyPhi (x/(24*x+1)) =
      fktyCuspPeriod (x : ℝ) := by
  have hd : cuspDenom transportMatrix34 x = 24*x+1 := by
    simp [cuspDenom, transportMatrix34]
  have ha : cuspAction transportMatrix34 x = x/(24*x+1) := by
    rw [cuspAction, hd]
    simp [transportMatrix34]
  have hstart : -(transportMatrix34 1 1 : ℚ) / (transportMatrix34 1 0 : ℚ) = -1/24 := by
    decide +kernel
  have h := hFKTY transportMatrix34 transportMatrix34_mem (by decide) (by decide) x he
    (by rw [hd]; linarith)
  rwa [hd, ha, transportMatrix34_multiplier, inv_one, mul_one, hstart,
    ← fktyCuspPeriod_rat] at h

end MockThetaAnalytic
