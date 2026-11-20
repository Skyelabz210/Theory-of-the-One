import ShadowGaussian
import Mathlib.Analysis.Convex.Deriv

/-! The real smoothing kernel of the FKTY integral at a lower-half-plane point.
Its convexity and monotone decay control summation by parts at a cusp. -/

noncomputable section

namespace MockThetaAnalytic

open Real Set Filter
open scoped Topology

/-- The radial smoothing profile at the dimensionless height variable v. -/
def eichlerProfile (v : ℝ) : ℝ := exp (v^2) * erfc (sqrt 2 * v)

@[simp] theorem eichlerProfile_zero : eichlerProfile 0 = 1 := by simp [eichlerProfile, erfc]

theorem eichlerProfile_nonneg (v : ℝ) (hv : 0 ≤ v) : 0 ≤ eichlerProfile v :=
  mul_nonneg (exp_pos _).le (erfc_nonneg _ (mul_nonneg (sqrt_nonneg _) hv))

private def slope (v : ℝ) : ℝ :=
  2*v*eichlerProfile v - (2*sqrt 2 / sqrt Real.pi)*exp (-(v^2))

private theorem hasDerivAt_profile (v : ℝ) : HasDerivAt eichlerProfile (slope v) v := by
  have hs : (sqrt 2)^2 = (2 : ℝ) := sq_sqrt (by norm_num)
  have h1 := ((hasDerivAt_id v).pow 2).exp
  have h2 := (hasDerivAt_erfc (sqrt 2 * v)).comp v ((hasDerivAt_id v).const_mul (sqrt 2))
  convert h1.mul h2 using 1
  simp only [slope, eichlerProfile, Function.comp_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
    pow_one, Nat.reduceSub, mul_one]
  have harg : -(sqrt 2 * v)^2 = -(v^2) + -(v^2) := by rw [mul_pow, hs]; ring
  rw [harg, exp_add, exp_neg]
  field_simp [(exp_pos (v^2)).ne']
  ring

private theorem hasDerivAt_slope (v : ℝ) :
    HasDerivAt slope ((2+4*v^2) * eichlerProfile v) v := by
  have h1 := (((hasDerivAt_id v).const_mul 2).mul (hasDerivAt_profile v))
  have h2 := (((((hasDerivAt_id v).pow 2).neg).exp).const_mul (2*sqrt 2 / sqrt Real.pi))
  convert h1.sub h2 using 1
  simp only [slope, id_eq, Pi.neg_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

/-- The special scale √2 cancels the inhomogeneous terms in the second derivative. -/
theorem deriv2_eichlerProfile (v : ℝ) :
    deriv (deriv eichlerProfile) v = (2 + 4*v^2) * eichlerProfile v := by
  rw [show deriv eichlerProfile = slope from funext (fun x => (hasDerivAt_profile x).deriv)]
  exact (hasDerivAt_slope v).deriv

theorem continuous_eichlerProfile : Continuous eichlerProfile :=
  continuous_iff_continuousAt.mpr fun v => (hasDerivAt_profile v).continuousAt

theorem convexOn_eichlerProfile : ConvexOn ℝ (Ici 0) eichlerProfile := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici _) continuous_eichlerProfile.continuousOn
    (fun v _ => (hasDerivAt_profile v).hasDerivWithinAt)
    (fun v _ => (hasDerivAt_slope v).hasDerivWithinAt)
  intro v hv
  exact mul_nonneg (by positivity) (eichlerProfile_nonneg v (interior_subset hv))

private theorem profile_tail {v : ℝ} (hv : 0 < v) :
    eichlerProfile v ≤ exp (-(v^2)) / (sqrt Real.pi * (sqrt 2 * v)) := by
  have hpos : 0 < sqrt 2 * v := by positivity
  have h := abs_erfc_le _ hpos
  rw [abs_of_nonneg (erfc_nonneg _ hpos.le)] at h
  apply (mul_le_mul_of_nonneg_left h (exp_pos _).le).trans_eq
  rw [← mul_div_assoc, ← exp_add]
  congr 2
  rw [mul_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

theorem antitoneOn_eichlerProfile : AntitoneOn eichlerProfile (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) continuous_eichlerProfile.continuousOn
    (fun v _ => (hasDerivAt_profile v).differentiableAt.differentiableWithinAt)
  intro v hv
  have hv' : 0 < v := by simpa using hv
  have hd : 0 < sqrt Real.pi * (sqrt 2 * v) := by positivity
  have he := (le_div_iff₀ hd).mp (profile_tail hv')
  rw [(hasDerivAt_profile v).deriv, slope]
  apply sub_nonpos.mpr
  rw [div_mul_eq_mul_div, le_div_iff₀ (sqrt_pos.2 pi_pos)]
  have hs : (sqrt 2)^2 = (2:ℝ) := sq_sqrt (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ 2*sqrt 2 by positivity),
    mul_nonneg (eichlerProfile_nonneg v hv'.le) (mul_nonneg (sqrt_nonneg Real.pi) hv'.le)]

private theorem profile_tail_one {v : ℝ} (hv : 1 ≤ v) :
    eichlerProfile v ≤ exp (-v) := by
  have h2 : 1 ≤ sqrt 2 := by norm_num
  have hp : 1 ≤ sqrt Real.pi := (le_sqrt (by norm_num) pi_pos.le).2 (by linarith [two_le_pi])
  have hden : 1 ≤ sqrt Real.pi * (sqrt 2 * v) := one_le_mul_of_one_le_of_one_le hp
    (one_le_mul_of_one_le_of_one_le h2 hv)
  exact (profile_tail (by linarith)).trans ((div_le_self (exp_pos _).le hden).trans
    (exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hv) (show 0 ≤ v by linarith)])))

theorem tendsto_eichlerProfile_atTop : Tendsto eichlerProfile atTop (𝓝 0) :=
  squeeze_zero' ((eventually_ge_atTop (0 : ℝ)).mono fun v hv => eichlerProfile_nonneg v hv)
    ((eventually_ge_atTop (1 : ℝ)).mono fun _ hv => profile_tail_one hv)
    tendsto_exp_neg_atTop_nhds_zero

private theorem summable_mesh_of_exp_bound (W : ℝ → ℝ) (hW : ∀ v, 0 ≤ v → 0 ≤ W v)
    (hbound : ∀ v, 1 ≤ v → W v ≤ exp (-v)) (h : ℝ) (hh : 0 < h) :
    Summable (fun m : ℕ => W ((m : ℝ)*h)) := by
  have hgeom := summable_geometric_of_norm_lt_one (x := exp (-h)) (by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_lt_one_iff]; linarith)
  apply hgeom.of_norm_bounded_eventually_nat
  have ht : Tendsto (fun m : ℕ => (m : ℝ)*h) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hh
  filter_upwards [ht.eventually_ge_atTop 1] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (hW _ (by positivity)), ← exp_nat_mul]
  simpa [mul_neg] using hbound _ hm

theorem summable_eichlerProfile_mesh (h : ℝ) (hh : 0 < h) :
    Summable (fun m : ℕ => eichlerProfile ((m : ℝ)*h)) :=
  summable_mesh_of_exp_bound _ eichlerProfile_nonneg (fun _ => profile_tail_one) h hh

/-- At a fixed real cusp, cutting off the vertical integral gives the plain erfc profile. -/
@[simp] theorem erfc_zero : erfc 0 = 1 := by simp [erfc]

theorem continuous_erfc : Continuous erfc :=
  continuous_iff_continuousAt.mpr fun v => (hasDerivAt_erfc v).continuousAt

theorem antitoneOn_erfc : AntitoneOn erfc (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) continuous_erfc.continuousOn
    (fun v _ => (hasDerivAt_erfc v).differentiableAt.differentiableWithinAt)
  intro v _
  rw [(hasDerivAt_erfc v).deriv]
  exact neg_nonpos.mpr (by positivity)

theorem convexOn_erfc : ConvexOn ℝ (Ici 0) erfc := by
  let d (v : ℝ) := -(2 / sqrt Real.pi * exp (-(v^2)))
  have h2 (v : ℝ) : HasDerivAt d (2 / sqrt Real.pi * exp (-(v^2)) * (2*v)) v := by
    convert (((((hasDerivAt_id v).pow 2).neg.exp).const_mul (2 / sqrt Real.pi))).neg using 1
    simp only [Pi.neg_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici _) continuous_erfc.continuousOn
    (fun v _ => (hasDerivAt_erfc v).hasDerivWithinAt) (fun v _ => (h2 v).hasDerivWithinAt)
  intro v hv
  have : 0 ≤ v := interior_subset hv
  positivity

private theorem erfc_le_exp_tail (v : ℝ) (hv : 1 ≤ v) : erfc v ≤ exp (-v) := by
  have hv' : 0 < v := by linarith
  have hp : 1 ≤ sqrt Real.pi := (le_sqrt (by norm_num) pi_pos.le).2 (by linarith [two_le_pi])
  have hden := one_le_mul_of_one_le_of_one_le hp hv
  exact (le_abs_self _).trans ((abs_erfc_le v hv').trans ((div_le_self (exp_pos _).le hden).trans
    (exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hv) hv'.le]))))

theorem tendsto_erfc_atTop : Tendsto erfc atTop (𝓝 0) :=
  squeeze_zero' ((eventually_ge_atTop (0 : ℝ)).mono fun v hv => erfc_nonneg v hv)
    ((eventually_ge_atTop (1 : ℝ)).mono fun v hv => erfc_le_exp_tail v hv)
    tendsto_exp_neg_atTop_nhds_zero

theorem summable_erfc_mesh (h : ℝ) (hh : 0 < h) :
    Summable (fun m : ℕ => erfc ((m : ℝ)*h)) :=
  summable_mesh_of_exp_bound _ erfc_nonneg erfc_le_exp_tail h hh

end MockThetaAnalytic
