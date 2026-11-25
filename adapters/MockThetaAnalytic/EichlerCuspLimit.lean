import FKTYCuspMoments
import FKTYCuspModes
import EichlerProfile
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Radial evaluation of the lower-half-plane Eichler integral for the FKTY
theta series. The contour starts at the conjugate of the argument when the
cutoff equals the positive depth below the real axis. -/

noncomputable section

namespace MockThetaAnalytic

open Complex MeasureTheory Set Filter KElimination.MockThetaShadow KElimination.ShadowConvergence
open scoped Topology

/-- Vertical integrand at x+it with lower-half-plane parameter x−iy. -/
def fktyEichlerIntegrand (x y t : ℝ) : ℂ :=
  I * fktyTheta ((x : ℂ) + t*I) /
    (((x : ℂ) + t*I - ((x : ℂ) - y*I)) ^ (1/2 : ℂ))

/-- Integrate from x+ib to x+i∞, using the principal square root. -/
def fktyEichlerTrunc (x b y : ℝ) : ℂ := ∫ t in Ioi b, fktyEichlerIntegrand x y t

private def rate : ℝ := Real.sqrt (Real.pi/12)

private theorem rate_pos : 0 < rate := Real.sqrt_pos.2 (by positivity)

private theorem rate_sq : rate^2 = Real.pi/12 := Real.sq_sqrt (by positivity)

theorem root_I_mul (v : ℝ) (hv : 0 < v) :
    ((v : ℂ)*I)^(1/2 : ℂ) = (Real.sqrt v : ℂ) * I^(1/2 : ℂ) := by
  have hc := Complex.ofReal_cpow hv.le (1/2)
  push_cast at hc
  rw [Real.sqrt_eq_rpow, hc]
  have hv' := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hv' I_ne_zero), log_ofReal_mul hv I_ne_zero,
    add_mul, Complex.exp_add, cpow_def_of_ne_zero hv', cpow_def_of_ne_zero I_ne_zero,
    ofReal_log hv.le]

private theorem root_I_sq : (I ^ (1/2 : ℂ)) ^ (2 : ℕ) = I := by
  rw [← cpow_mul_nat]
  norm_num

private theorem scale_eq : fktyScale = (Real.sqrt Real.pi / rate : ℝ) * I^(1/2 : ℂ) := by
  rw [fktyScale, ← Complex.ofReal_ofNat 12, root_I_mul _ (by norm_num)]
  congr 2
  rw [rate, Real.sqrt_div Real.pi_pos.le]
  field_simp [Real.sqrt_pos.2 Real.pi_pos]

private theorem shadowTerm_ray (x t : ℝ) (m : ℕ) :
    shadowTerm (shadowNome ((x : ℂ) + t*I)) m =
      fktyCuspCoefficient (integerNome ((x : ℂ)/24)) m *
        (gaussianMode (Real.pi/12) m t : ℂ) := by
  unfold shadowTerm shadowNome fktyCuspCoefficient integerNome gaussianMode shadowWeight
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  push_cast
  have hexp : (m : ℂ)^2 * ((2 * Real.pi / 24 * (x + (t : ℂ)*I)) * I) =
      (m : ℂ)^2 * (2*Real.pi*I*(x/24)) + -(Real.pi / 12 * (m : ℂ)^2) * t := by
    ring_nf
    simp [I_sq]
    ring
  rw [hexp, Complex.exp_add]
  ring

theorem fktyTheta_ray (x t : ℝ) (ht : 0 < t) :
    fktyTheta ((x : ℂ)+t*I) = 2 * ∑' m, fktyCuspCoefficient (integerNome ((x : ℂ)/24)) m *
      (gaussianMode (Real.pi/12) m t : ℂ) := by
  rw [fktyTheta_eq_shadowSeries _ (by simpa using ht), shadowSeries]
  simp_rw [shadowTerm_ray]

private def rayMode (m : ℕ) (y t : ℝ) : ℝ :=
  gaussianMode (Real.pi/12) m t / Real.sqrt (t+y)

private def modeTail (m : ℕ) (b y : ℝ) : ℝ :=
  Real.exp ((rate*m)^2*y) * erfc (rate*m*Real.sqrt (b+y))

private theorem erfc_tendsto_zero : Tendsto erfc atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => 1/(Real.sqrt Real.pi*x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (Real.sqrt_pos.2 Real.pi_pos))
  apply squeeze_zero' _ _ h
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx using erfc_nonneg x hx.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (le_abs_self _).trans ((abs_erfc_le x hx).trans (div_le_div_of_nonneg_right
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg x))) (by positivity)))

private theorem mode_primitive (m : ℕ) (y t : ℝ) (ht : 0 < t+y) :
    HasDerivAt (fun s => -(Real.sqrt Real.pi/rate)*modeTail m s y) (rayMode m y t) t := by
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have hcomp := hs.comp t ((hasDerivAt_id t).add_const y)
  have h := ((((hasDerivAt_erfc _).comp t (hcomp.const_mul (rate*m))).const_mul
    (Real.exp ((rate*m)^2*y))).const_mul (-(Real.sqrt Real.pi/rate)))
  convert h using 1
  dsimp [rayMode, gaussianMode]
  have harg : -(rate * (m : ℝ) * Real.sqrt (t+y))^2 =
      -(rate*(m : ℝ))^2*y + -(Real.pi/12*(m : ℝ)^2)*t := by
    rw [mul_pow, Real.sq_sqrt ht.le, mul_pow, rate_sq]
    ring
  rw [harg, Real.exp_add, neg_mul, Real.exp_neg]
  field_simp [rate_pos.ne', (Real.sqrt_pos.2 ht).ne', (Real.sqrt_pos.2 Real.pi_pos).ne']
  ring_nf
  rw [Real.exp_neg]
  field_simp

private theorem mode_primitive_limit (m : ℕ) (hm : 0 < m) (y : ℝ) :
    Tendsto (fun t => -(Real.sqrt Real.pi/rate)*modeTail m t y) atTop (𝓝 0) := by
  have hs : Tendsto (fun t : ℝ => Real.sqrt (t+y)) atTop atTop := by
    apply tendsto_atTop.2
    intro c
    filter_upwards [eventually_ge_atTop (c^2-y)] with t ht
    exact (Real.le_sqrt_of_sq_le (by linarith))
  have hp : 0 < rate*(m : ℝ) := mul_pos rate_pos (by exact_mod_cast hm)
  simpa [modeTail] using
    ((erfc_tendsto_zero.comp (hs.const_mul_atTop hp)).const_mul (Real.exp ((rate*m)^2*y))).const_mul
      (-(Real.sqrt Real.pi/rate))

private theorem eval_mode (m : ℕ) (hm : 0 < m) (b y : ℝ) (hb : 0 < b) (hy : 0 ≤ y) :
    (∫ t in Ioi b, rayMode m y t) = (Real.sqrt Real.pi/rate)*modeTail m b y := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := b)
    (fun t (ht : b ≤ t) => mode_primitive m y t (by linarith))
    (fun t _ => by dsimp [rayMode, gaussianMode]; positivity) (mode_primitive_limit m hm y)
  simpa using h

private theorem summable_modeTail (b y : ℝ) (hb : 0 < b) (hy : 0 ≤ y) :
    Summable (fun m : ℕ => modeTail m b y) := by
  let C := (Real.sqrt Real.pi * (rate * Real.sqrt (b+y)))⁻¹
  have hby : 0 < b+y := by linarith
  have hbase := Real.summable_exp_nat_mul_of_ge (c := -(rate^2*b))
    (by nlinarith [sq_pos_of_pos rate_pos, mul_pos (sq_pos_of_pos rate_pos) hb])
    (f := fun m : ℕ => (m:ℝ)^2) (fun m => by
      change (m : ℝ) ≤ (m : ℝ)^2
      exact_mod_cast (show m ≤ m^2 by nlinarith [Nat.le_mul_self m]))
  apply (hbase.mul_left C).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hpos : 0 < rate*m*Real.sqrt (b+y) := by
    have := rate_pos
    positivity
  dsimp only [modeTail]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp ((rate*m)^2*y) *
        (Real.exp (-(rate*m*Real.sqrt (b+y))^2) / (Real.sqrt Real.pi*(rate*m*Real.sqrt (b+y)))) :=
      mul_le_mul_of_nonneg_left (abs_erfc_le _ hpos) (Real.exp_pos _).le
    _ = Real.exp (-(rate^2*b)*(m:ℝ)^2) / (Real.sqrt Real.pi*(rate*m*Real.sqrt (b+y))) := by
      rw [mul_div_assoc', ← Real.exp_add]
      congr 2
      simp only [mul_pow, Real.sq_sqrt hby.le]
      ring
    _ ≤ _ := by
      rw [mul_comm C, ← div_eq_mul_inv]
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by have := rate_pos; positivity)
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      simpa using mul_le_mul_of_nonneg_left hm' rate_pos.le

private theorem mode_integrable (m : ℕ) (b y : ℝ) (hb : 0 < b) (hy : 0 ≤ y) :
    IntegrableOn (rayMode m y) (Ioi b) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · unfold rayMode gaussianMode
    simp [IntegrableOn]
  · exact integrableOn_Ioi_deriv_of_nonneg'
      (fun t (ht : b ≤ t) => mode_primitive m y t (by linarith))
      (fun t _ => by dsimp [rayMode, gaussianMode]; positivity) (mode_primitive_limit m hm y)

private theorem norm_rayCoeff (x : ℝ) (m : ℕ) :
    ‖fktyCuspCoefficient (integerNome ((x : ℂ)/24)) m‖ ≤ 1 := by
  have hn : ‖integerNome ((x : ℂ)/24)‖ = 1 := by
    simp [integerNome, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  simp only [fktyCuspCoefficient, norm_mul, norm_pow, hn, one_pow, mul_one]
  unfold shadowSign
  split_ifs <;> norm_num

/-- Exact Fourier evaluation of the integral, valid for an arbitrary real cusp,
positive cutoff, and nonnegative depth. At b=y this is the actual lower Eichler
integral. Putting y=0 gives the vertically truncated real-boundary integral. -/
private theorem eichlerTrunc_evaluation (x b y : ℝ) (hb : 0 < b) (hy : 0 ≤ y) :
    IntegrableOn (fktyEichlerIntegrand x y) (Ioi b) ∧
    fktyEichlerTrunc x b y = 2 * fktyScale *
      ∑' m : ℕ, fktyCuspCoefficient (integerNome ((x : ℂ)/24)) m *
        ((Real.exp ((rate*m)^2*y) * erfc (rate*m*Real.sqrt (b+y)) : ℝ) : ℂ) := by
  let c (m : ℕ) := fktyCuspCoefficient (integerNome ((x : ℂ)/24)) m
  let F (m : ℕ) (t : ℝ) := c m * (rayMode m y t : ℂ)
  have hc0 : c 0 = 0 := by simp [c, fktyCuspCoefficient, shadowSign]
  have hi m : IntegrableOn (F m) (Ioi b) := (mode_integrable m b y hb hy).ofReal.const_mul _
  have hn (m : ℕ) : (∫ t in Ioi b, ‖F m t‖) =
      ‖c m‖ * ((Real.sqrt Real.pi/rate) * modeTail m b y) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [F, hc0]
    · have habs (t : ℝ) : |rayMode m y t| = rayMode m y t := abs_of_nonneg (by dsimp [rayMode, gaussianMode]; positivity)
      simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs, habs]
      rw [integral_const_mul, eval_mode _ hm _ _ hb hy]
  have hs : Summable (fun m => ∫ t in Ioi b, ‖F m t‖) := by
    apply ((summable_modeTail b y hb hy).mul_left (Real.sqrt Real.pi/rate)).of_nonneg_of_le
      (fun m => integral_nonneg fun t => norm_nonneg _)
    intro m
    rw [hn]
    have ht : 0 ≤ modeTail m b y := by
      apply mul_nonneg (Real.exp_pos _).le
      apply erfc_nonneg
      exact mul_nonneg (mul_nonneg rate_pos.le (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
    simpa using mul_le_mul_of_nonneg_right (norm_rayCoeff x m)
      (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) rate_pos.le) ht)
  have hsum := integral_tsum_of_summable_integral_norm hi hs
  have hval (m : ℕ) : (∫ t in Ioi b, F m t) =
      (Real.sqrt Real.pi/rate : ℝ) * (c m * (modeTail m b y : ℂ)) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [F, hc0]
    · rw [show (∫ t in Ioi b, F m t) = c m * (↑(∫ t in Ioi b, rayMode m y t) : ℂ) by
            unfold F
            rw [integral_const_mul]
            congr 1
            exact integral_ofReal (f := rayMode m y) (𝕜 := ℂ), eval_mode m hm b y hb hy]
      push_cast
      ring
  have hir : I^(1/2:ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl I_ne_zero)
  have hk (t : ℝ) (ht : b < t) :
      I * fktyTheta ((x : ℂ)+t*I) / (((x : ℂ)+t*I-(x-y*I))^(1/2:ℂ)) =
        (2*I^(1/2:ℂ)) * ∑' m, F m t := by
    have hty : 0 < t+y := by linarith
    have hrt : (Real.sqrt (t+y) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.2 hty).ne'
    rw [show ((x : ℂ)+t*I-(x-y*I)) = ((t+y : ℝ) : ℂ)*I by push_cast; ring,
      root_I_mul _ hty, fktyTheta_ray _ _ (hb.trans ht)]
    have hf m : F m t = (Real.sqrt (t+y) : ℂ)⁻¹ *
        (fktyCuspCoefficient (integerNome ((x : ℂ)/24)) m * (gaussianMode (Real.pi/12) m t : ℂ)) := by
      dsimp [F, c, rayMode]
      push_cast
      ring
    simp_rw [hf]
    rw [tsum_mul_left]
    field_simp
    linear_combination (norm := ring_nf) 2 * (∑' m, fktyCuspCoefficient (integerNome ((x : ℂ)/24)) m *
      (gaussianMode (Real.pi/12) m t : ℂ)) * root_I_sq.symm
    rw [root_I_sq]
    ring
  have hint := (integrable_tsum_of_summable_integral_norm F hi hs).const_mul (2*I^(1/2:ℂ))
  change ∀ t, b < t → fktyEichlerIntegrand x y t = (2*I^(1/2:ℂ)) * ∑' m, F m t at hk
  refine ⟨IntegrableOn.congr_fun hint (fun t ht => (hk t ht).symm) measurableSet_Ioi, ?_⟩
  rw [fktyEichlerTrunc, setIntegral_congr_fun measurableSet_Ioi hk, integral_const_mul, ← hsum]
  simp_rw [hval]
  rw [tsum_mul_left, scale_eq]
  dsimp only [c, modeTail]
  ring

theorem integrableOn_fktyEichlerTrunc (x b y : ℝ) (hb : 0 < b) (hy : 0 ≤ y) :
    IntegrableOn (fktyEichlerIntegrand x y) (Ioi b) :=
  (eichlerTrunc_evaluation x b y hb hy).1

/-- The signed finite-cusp coefficients give the Fourier expansion for any
positive cutoff and nonnegative depth below the real axis. -/
theorem fktyEichlerTrunc_eq_series (x b y : ℝ) (hb : 0 < b) (hy : 0 ≤ y) :
    fktyEichlerTrunc x b y = 2 * fktyScale *
      ∑' m : ℕ, fktyCuspCoefficient (integerNome ((x : ℂ)/24)) m *
        ((Real.exp ((Real.sqrt (Real.pi/12)*m)^2*y) *
          erfc (Real.sqrt (Real.pi/12)*m*Real.sqrt (b+y)) : ℝ) : ℂ) :=
  (eichlerTrunc_evaluation x b y hb hy).2

/-- The published lower argument x−ib has conjugate starting point x+ib.
Its damping profile includes the positive exponential multiplying erfc. -/
theorem fktyEichlerTrunc_eq_lower_series (x b : ℝ) (hb : 0 < b) :
    fktyEichlerTrunc x b b = 2 * fktyScale *
      ∑' m : ℕ, fktyCuspCoefficient (integerNome ((x : ℂ)/24)) m *
        (eichlerProfile ((m:ℝ)*Real.sqrt (Real.pi/12*b)) : ℂ) := by
  rw [fktyEichlerTrunc_eq_series x b b hb hb.le]
  congr 1
  apply tsum_congr
  intro m
  congr 2
  unfold eichlerProfile
  have ha : 0 ≤ Real.pi/12 := by positivity
  have htwo : b+b = 2*b := by ring
  rw [htwo, Real.sqrt_mul ha, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 2
  · simp only [mul_pow, Real.sq_sqrt hb.le]; ring
  · ring

/-- Keeping the kernel parameter at the real cusp gives the ordinary
complementary-error-function cutoff instead. -/
theorem fktyEichlerTrunc_eq_boundary_series (x b : ℝ) (hb : 0 < b) :
    fktyEichlerTrunc x b 0 = 2 * fktyScale *
      ∑' m : ℕ, fktyCuspCoefficient (integerNome ((x : ℂ)/24)) m *
        (erfc ((m:ℝ)*Real.sqrt (Real.pi/12*b)) : ℂ) := by
  rw [fktyEichlerTrunc_eq_series x b 0 hb le_rfl]
  simp only [mul_zero, Real.exp_zero, one_mul, add_zero, Real.sqrt_mul (by positivity : 0 ≤ Real.pi/12)]
  have hm (m : ℕ) : Real.sqrt (Real.pi/12) * m * Real.sqrt b =
      m * (Real.sqrt (Real.pi/12) * Real.sqrt b) := by ring
  simp_rw [hm]

end MockThetaAnalytic
