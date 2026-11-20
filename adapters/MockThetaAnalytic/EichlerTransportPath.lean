import FKTYPeriodRegularity

/-! Pullback of the order-10 vertical ray by the inverse of the FKTY matrix.
The resulting arc runs from the order-34 cusp to the pole at −1/24. -/

noncomputable section
namespace MockThetaAnalytic
open Complex Filter Set
open scoped Topology

/-- Fractional linear action of the matrix with lower row (24,1). -/
def eichlerTransportMap (z : ℂ) : ℂ := z / (24*z + 1)

/-- Height parametrization of the target vertical ray. -/
def eichlerTargetRay (t : ℝ) : ℂ := -1/10 + (t : ℂ)*I

/-- Pullback of the vertical ray above −1/10. -/
def eichlerInverseRay (t : ℝ) : ℂ := eichlerTargetRay t / (1-24*eichlerTargetRay t)

def eichlerRayDenom (t : ℝ) : ℝ := (17/5)^2 + (24*t)^2

private theorem denom_pos (t : ℝ) : 0 < eichlerRayDenom t := by
  unfold eichlerRayDenom
  positivity

private theorem denom_re (t : ℝ) : (1-24*eichlerTargetRay t).re = 17/5 := by
  norm_num [eichlerTargetRay, mul_re, div_re, normSq_apply]

private theorem denom_im (t : ℝ) : (1-24*eichlerTargetRay t).im = -(24*t) := by
  norm_num [eichlerTargetRay, mul_im, div_im, normSq_apply]

private theorem ray_denom_ne (t : ℝ) : 1-24*eichlerTargetRay t ≠ 0 := by
  intro h
  have h' := denom_re t
  rw [h] at h'
  norm_num at h'

/-- Both heights are positive at every interior point of the arc. -/
theorem eichlerInverseRay_coordinates (t : ℝ) :
    (eichlerInverseRay t).im = t / eichlerRayDenom t ∧
    (eichlerInverseRay t).re = -1/24 + 17/(120*eichlerRayDenom t) := by
  have hsq : normSq (1-24*eichlerTargetRay t) = eichlerRayDenom t := by
    rw [normSq_apply, denom_re, denom_im, eichlerRayDenom]; ring
  have hre : (eichlerTargetRay t).re = -1/10 := by norm_num [eichlerTargetRay, div_re, normSq_apply]
  have him : (eichlerTargetRay t).im = t := by norm_num [eichlerTargetRay, div_im, normSq_apply]
  have h := (denom_pos t).ne'
  constructor
  · rw [eichlerInverseRay, div_im, hsq, hre, him, denom_im, denom_re]; ring
  · rw [eichlerInverseRay, div_re, hsq, hre, him, denom_im, denom_re]
    field_simp; unfold eichlerRayDenom; ring

theorem eichlerInverseRay_im_pos (t : ℝ) (ht : 0<t) : 0 < (eichlerInverseRay t).im := by
  rw [(eichlerInverseRay_coordinates t).1]
  exact div_pos ht (denom_pos t)

theorem eichlerTransportMap_inverseRay (t : ℝ) :
    eichlerTransportMap (eichlerInverseRay t) = eichlerTargetRay t := by
  have h := ray_denom_ne t
  have hj : 24*eichlerInverseRay t + 1 = (1-24*eichlerTargetRay t)⁻¹ := by
    unfold eichlerInverseRay; field_simp; ring
  rw [eichlerTransportMap, hj, div_inv_eq_mul]
  exact div_mul_cancel₀ _ h

theorem eichlerInverseRay_hasDerivAt (t : ℝ) :
    HasDerivAt eichlerInverseRay (I/(1-24*eichlerTargetRay t)^2) t := by
  have hw : HasDerivAt eichlerTargetRay I t := by
    unfold eichlerTargetRay
    simpa only [ofRealCLM_apply, ofReal_one, one_mul] using
      ((ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add (-1/10 : ℂ)
  have hd := (hw.const_mul 24).const_sub 1
  convert hw.div hd (ray_denom_ne t) using 1
  ring

private theorem re_shift34 (t : ℝ) :
    (eichlerInverseRay t).re - (-1/34) = -(120/17)*t^2/eichlerRayDenom t := by
  rw [(eichlerInverseRay_coordinates t).2]
  field_simp [(denom_pos t).ne']; unfold eichlerRayDenom; ring

theorem eichlerInverseRay_offset_zero :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      |(eichlerInverseRay t).re - (-1/34)| ≤ 5000 * (eichlerInverseRay t).im^2 := by
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with t ht
  rw [re_shift34, abs_of_nonpos (by apply div_nonpos_of_nonpos_of_nonneg <;> first | positivity | nlinarith [sq_nonneg t] | exact (denom_pos t).le),
    (eichlerInverseRay_coordinates t).1]
  have hsmall : eichlerRayDenom t ≤ 600 := by
    unfold eichlerRayDenom
    have := sq_le_sq' (by linarith [ht.1] : -(1:ℝ) ≤ t) ht.2.le
    nlinarith
  field_simp [(denom_pos t)]
  nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hsmall)]

theorem eichlerInverseRay_offset_infty :
    ∀ᶠ t : ℝ in atTop,
      |(eichlerInverseRay t).re - (-1/24)| ≤ 100 * (eichlerInverseRay t).im^2 := by
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  rw [(eichlerInverseRay_coordinates t).2, add_sub_cancel_left, abs_of_nonneg (by positivity [denom_pos t]),
    (eichlerInverseRay_coordinates t).1]
  field_simp [denom_pos t]
  unfold eichlerRayDenom
  nlinarith [sq_le_sq' (by linarith : -(t:ℝ) ≤ 1) ht]

theorem eichlerInverseRay_height_zero :
    Tendsto (fun t => (eichlerInverseRay t).im) (𝓝[>] (0:ℝ)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simp_rw [(eichlerInverseRay_coordinates _).1]
    have h : ContinuousAt (fun t => t/eichlerRayDenom t) 0 := by
      apply continuousAt_id.div _ (denom_pos 0).ne'
      unfold eichlerRayDenom; fun_prop
    simpa using h.continuousWithinAt.tendsto (s := Ioi 0)
  · filter_upwards [self_mem_nhdsWithin] with t ht using eichlerInverseRay_im_pos t ht

theorem eichlerInverseRay_height_infty :
    Tendsto (fun t => (eichlerInverseRay t).im) atTop (𝓝[>] 0) := by
  have hp : ∀ᶠ t : ℝ in atTop, 0<t := eventually_gt_atTop _
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, hp.mono fun t ht => eichlerInverseRay_im_pos t ht⟩
  apply squeeze_zero' (hp.mono fun t ht => (eichlerInverseRay_im_pos t ht).le) _ tendsto_inv_atTop_zero
  filter_upwards [hp] with t ht
  rw [(eichlerInverseRay_coordinates t).1, ← one_div]
  apply (div_le_div_iff₀ (denom_pos _) ht).mpr
  unfold eichlerRayDenom; nlinarith [sq_nonneg t]

private theorem jacobian_inverseRay (t : ℝ) :
    24*eichlerInverseRay t + 1 = (1-24*eichlerTargetRay t)⁻¹ := by
  unfold eichlerInverseRay
  field_simp [ray_denom_ne t]
  ring

private theorem inverseRay_root_factor (t : ℝ) (ht : 0<t) :
    (eichlerInverseRay t - (-1/34))^(1/2:ℂ) =
      (5/17:ℂ)^(1/2:ℂ) * (((t:ℂ)*I)^(1/2:ℂ)) * (24*eichlerInverseRay t+1)^(1/2:ℂ) := by
  let j := 24*eichlerInverseRay t + 1
  have hj : j ≠ 0 := by dsimp [j]; rw [jacobian_inverseRay]; exact inv_ne_zero (ray_denom_ne t)
  have hjre : 0 < j.re := by
    dsimp [j]
    rw [(eichlerInverseRay_coordinates t).2]
    norm_num
    have h := denom_pos t
    field_simp
    linarith
  have hti : (t:ℂ)*I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr ht.ne') I_ne_zero
  have harg := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hjre)
  have hlog : log (((t:ℂ)*I)*j) = log ((t:ℂ)*I) + log j := by
    apply Complex.log_mul hti hj
    rw [arg_real_mul _ ht, arg_I]
    constructor <;> linarith [abs_lt.mp harg |>.1, abs_lt.mp harg |>.2, Real.pi_pos]
  have hval : eichlerInverseRay t - (-1/34) = ((5/17:ℝ):ℂ) * (((t:ℂ)*I)*j) := by
    dsimp [j]
    rw [jacobian_inverseRay, eichlerInverseRay]
    let D := 1-24*eichlerTargetRay t
    have hD : D ≠ 0 := ray_denom_ne t
    change eichlerTargetRay t / D - (-1/34) = ((5/17:ℝ):ℂ) * (((t:ℂ)*I)*D⁻¹)
    push_cast
    field_simp [hD]
    dsimp [D, eichlerTargetRay]
    ring
  have hroot := Complex.log_ofReal_mul (by norm_num : (0:ℝ)<5/17) (mul_ne_zero hti hj)
  rw [hval, cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr (by norm_num)) (mul_ne_zero hti hj)),
    hroot, hlog, cpow_def_of_ne_zero (by norm_num : (5/17:ℂ) ≠ 0),
    cpow_def_of_ne_zero hti, cpow_def_of_ne_zero hj]
  have hscale : log (5/17:ℂ) = (Real.log (5/17) : ℂ) := by
    simpa only [ofReal_div, ofReal_ofNat] using (ofReal_log (by norm_num : (0:ℝ) ≤ 5/17)).symm
  rw [hscale]
  simp only [add_mul, exp_add, mul_assoc]

/-- After the fractional-linear substitution, the complex Jacobian, theta
automorphy factor and two principal square roots leave the constant √(17/5). -/
theorem eichlerInverseRay_pullback (t : ℝ) (ht : 0<t)
    (hθ : fktyTheta (eichlerTransportMap (eichlerInverseRay t)) =
      (24*eichlerInverseRay t+1)^(3/2:ℂ) * fktyTheta (eichlerInverseRay t)) :
    (I/(1-24*eichlerTargetRay t)^2) * fktyTheta (eichlerInverseRay t) /
        ((eichlerInverseRay t - (-1/34))^(1/2:ℂ)) =
      (Real.sqrt (17/5):ℂ) * (I * fktyTheta (eichlerTargetRay t) / (((t:ℂ)*I)^(1/2:ℂ))) := by
  let j := 24*eichlerInverseRay t+1
  have hj : j ≠ 0 := by dsimp [j]; rw [jacobian_inverseRay]; exact inv_ne_zero (ray_denom_ne t)
  have hj2 : (1-24*eichlerTargetRay t)⁻¹ ^ 2 = j^2 := by rw [← jacobian_inverseRay]
  have hjs : j^2 = j^(3/2:ℂ) * j^(1/2:ℂ) := by
    rw [← cpow_add _ _ hj, show (3/2:ℂ)+1/2=2 by norm_num, cpow_ofNat]
  have hscale : (5/17:ℂ)^(-(1/2):ℂ) = (Real.sqrt (17/5):ℂ) := by
    have h := transportMatrix34_weight
    rw [transportMatrix34_cusps.2.2.1] at h
    push_cast at h
    convert h using 2
    ring
  have hroot : j^(1/2:ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hj)
  rw [eichlerTransportMap_inverseRay] at hθ
  rw [inverseRay_root_factor t ht, ← hscale, cpow_neg]
  rw [div_eq_mul_inv I, ← inv_pow, hj2, hjs, hθ]
  change _ / (_ * _ * j^(1/2:ℂ)) = _
  field_simp
  ring

/-- Derivative of a primitive along the arc. The local theta transformation
is the only modular identity needed for this substitution. -/
theorem hasDerivAt_eichlerPrimitive_inverseRay (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (fktyTheta z / ((z-(-1/34))^(1/2:ℂ))) z)
    (t : ℝ) (ht : 0<t)
    (hθ : fktyTheta (eichlerTransportMap (eichlerInverseRay t)) =
      (24*eichlerInverseRay t+1)^(3/2:ℂ) * fktyTheta (eichlerInverseRay t)) :
    HasDerivAt (fun v => F (eichlerInverseRay v))
      ((Real.sqrt (17/5):ℂ) * (I * fktyTheta (eichlerTargetRay t) /
        ((eichlerTargetRay t - (-1/10))^(1/2:ℂ)))) t := by
  have hf := (hF _ (eichlerInverseRay_im_pos t ht)).scomp t (eichlerInverseRay_hasDerivAt t)
  rw [smul_eq_mul, ← mul_div_assoc, eichlerInverseRay_pullback t ht hθ] at hf
  simpa only [eichlerTargetRay, add_sub_cancel_left] using hf

end MockThetaAnalytic
