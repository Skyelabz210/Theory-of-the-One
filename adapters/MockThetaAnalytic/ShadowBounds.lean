import ShadowGaussian
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Tactic.Linarith

/-! Uniform bounds for the nonholomorphic correction modes of the third-order
mock theta function and their real Fréchet derivatives on closed upper strips. -/

noncomputable section

namespace MockThetaAnalytic

open Complex KElimination.MockThetaShadow

private def angularFrequency (m : ℕ) : ℝ := 2 * Real.pi * (m : ℝ) ^ 2

private def tailConstant (a : ℝ) : ℝ := 2 / (Real.sqrt Real.pi * Real.sqrt a)

/-- A common summable upper bound for a correction mode and its first real
derivative throughout the region Im(z) ≥ a, for a > 0. -/
def modeMajorant (a : ℝ) (m : ℕ) : ℝ :=
  (tailConstant a + tailConstant a * angularFrequency m + 4 / Real.sqrt a * m) *
    Real.exp (-(2 * Real.pi * a)) ^ m

theorem modeMajorant_summable (a : ℝ) (ha : 0 < a) : Summable (modeMajorant a) := by
  let r := Real.exp (-(2 * Real.pi * a))
  have hr : ‖r‖ < 1 := by
    dsimp [r]
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos (by positivity) ha)
  have h (k : ℕ) := summable_pow_mul_geometric_of_norm_lt_one k hr
  have hs := ((((h 0).mul_left (tailConstant a)).add
    ((h 2).mul_left (tailConstant a * (2 * Real.pi)))).add ((h 1).mul_left (4 / Real.sqrt a)))
  apply hs.congr
  intro m
  simp only [modeMajorant, angularFrequency, pow_zero, pow_one, one_mul, r]
  ring

private theorem sign_abs_le (m : ℕ) : |(shadowSign m : ℝ)| ≤ 1 := by
  unfold shadowSign
  split
  · norm_num
  · split <;> norm_num

private theorem amplitude_le {a y : ℝ} (ha : 0 < a) (hy : a ≤ y)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (he : |ε| ≤ 1) :
    |modeAmplitude ε m y| ≤ tailConstant a * Real.exp (-(2 * angularFrequency m * y)) := by
  let x := Real.sqrt (4 * Real.pi * (m : ℝ)^2 * y)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hy0 := ha.trans_le hy
  have hx : 0 < x := by dsimp [x]; positivity
  have hx2 : x ^ 2 = 2 * angularFrequency m * y := by
    dsimp [x, angularFrequency]
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hscale : 1 ≤ 4 * Real.pi * (m : ℝ)^2 := by
    calc
      1 ≤ 4 * Real.pi * 1 := by linarith [Real.two_le_pi]
      _ ≤ 4 * Real.pi * (m : ℝ)^2 := by gcongr; nlinarith
  have hxa : Real.sqrt a ≤ x := Real.sqrt_le_sqrt (hy.trans (by
    simpa using mul_le_mul_of_nonneg_right hscale hy0.le))
  have htail := (abs_erfc_le x hx).trans (div_le_div_of_nonneg_left (Real.exp_pos _).le
    (mul_pos (Real.sqrt_pos.2 Real.pi_pos) (Real.sqrt_pos.2 ha))
    (mul_le_mul_of_nonneg_left hxa (Real.sqrt_nonneg _)))
  rw [hx2] at htail
  change |(-2 * ε) * erfc x| ≤ _
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ (2 * 1) * (Real.exp (-(2 * angularFrequency m * y)) / (Real.sqrt Real.pi * Real.sqrt a)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) htail (abs_nonneg _) (by norm_num)
    _ = _ := by unfold tailConstant; ring

private theorem amplitude_mul_fderiv_bound {A : ℝ → ℝ} {g : ℂ → ℂ} {z : ℂ}
    {v : ℝ} {b : ℂ} (ha : HasDerivAt A v z.im) (hg : HasDerivAt g b z) :
    ‖fderiv ℝ (fun w : ℂ => (A w.im : ℂ) * g w) z‖ ≤ |A z.im| * ‖b‖ + ‖g z‖ * |v| := by
  have hA := Complex.ofRealCLM.hasFDerivAt.comp z
    (ha.comp_hasFDerivAt z Complex.imCLM.hasFDerivAt)
  have hd : fderiv ℝ (fun w : ℂ => (A w.im : ℂ) * g w) z =
      (A z.im : ℂ) • (b • (1 : ℂ →L[ℝ] ℂ)) + g z • ofRealCLM.comp (v • imCLM) :=
    (hA.mul hg.complexToReal_fderiv).fderiv
  rw [hd]
  apply (norm_add_le _ _).trans
  have hc := ofRealCLM.opNorm_comp_le (v • imCLM)
  simp only [Complex.ofRealCLM_norm, norm_smul, Real.norm_eq_abs, Complex.imCLM_norm,
    mul_one, one_mul] at hc
  simp only [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hc (norm_nonneg (g z))) _

private theorem exp_decay_le (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : a ≤ z.im) (m : ℕ) :
    Real.exp (-(angularFrequency m * z.im)) ≤ Real.exp (-(2 * Real.pi * a)) ^ m := by
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  have hsq : (m : ℝ) ≤ (m : ℝ)^2 := by exact_mod_cast Nat.le_self_pow (by decide : 2 ≠ 0) m
  have h := mul_le_mul hsq hz ha.le (sq_nonneg (m : ℝ))
  unfold angularFrequency
  nlinarith [mul_le_mul_of_nonneg_left h (show 0 ≤ 2*Real.pi by positivity)]

private theorem bounds_pos (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : a ≤ z.im)
    (m : ℕ) (hm : 0 < m) :
    ‖nonholomorphicMode (shadowSign m : ℝ) m z‖ ≤ modeMajorant a m ∧
    ‖fderiv ℝ (nonholomorphicMode (shadowSign m : ℝ) m) z‖ ≤ modeMajorant a m := by
  let ε : ℝ := shadowSign m
  let ν := angularFrequency m
  let E := Real.exp (-(2 * ν * z.im))
  let G := Real.exp (ν * z.im)
  let g := fun w : ℂ => Complex.exp (-(ν : ℂ) * I * w)
  let c : ℂ := -(ν : ℂ) * I
  let v := 4 * ε * m * E / Real.sqrt z.im
  have hy := ha.trans_le hz
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hν : 0 ≤ ν := by dsimp [ν, angularFrequency]; positivity
  have hK : 0 ≤ tailConstant a := by unfold tailConstant; positivity
  have hA : |modeAmplitude ε m z.im| ≤ tailConstant a * E := amplitude_le ha hz m hm ε (sign_abs_le _)
  have hv : HasDerivAt (modeAmplitude ε m) v z.im := by
    convert hasDerivAt_modeAmplitude ε m z.im hm' hy using 1
    dsimp [v, E, ν, angularFrequency]
    ring_nf
  have hvb : |v| ≤ (4 / Real.sqrt a * m) * E := by
    dsimp only [v]
    have hE : 0 ≤ E := (Real.exp_pos _).le
    simp only [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg hm'.le, abs_of_nonneg hE,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ (4 * 1 * m * E) / Real.sqrt a := by
        apply div_le_div₀
        · positivity
        · gcongr
          exact sign_abs_le m
        · exact Real.sqrt_pos.2 ha
        · exact Real.sqrt_le_sqrt hz
      _ = _ := by ring
  have hg : HasDerivAt g (g z * c) z := by
    simpa [g, c] using ((hasDerivAt_id z).const_mul c).cexp
  have hc : ‖c‖ = ν := by simp [c, abs_of_nonneg hν]
  have hgNorm : ‖g z‖ = G := by
    simp [g, G, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hprod : E * G = Real.exp (-(ν * z.im)) := by
    dsimp [E, G]
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : 0 ≤ 4 / Real.sqrt a * m := by positivity
  have hvν : 0 ≤ tailConstant a * ν := mul_nonneg hK hν
  have hexp := exp_decay_le a ha z hz m
  have hmajor {B : ℝ} (hB : B ≤ tailConstant a + tailConstant a * ν + 4 / Real.sqrt a * m) :
      B * (E * G) ≤ modeMajorant a m := by
    rw [hprod]
    apply mul_le_mul hB hexp (Real.exp_pos _).le
    positivity
  constructor
  · change ‖(modeAmplitude ε m z.im : ℂ) * g z‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hgNorm]
    calc
      _ ≤ (tailConstant a * E) * G := mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
      _ = tailConstant a * (E * G) := mul_assoc _ _ _
      _ ≤ _ := hmajor (by linarith)
  · have hd := amplitude_mul_fderiv_bound hv hg
    rw [norm_mul, hgNorm, hc] at hd
    apply hd.trans
    calc
      _ ≤ (tailConstant a * E) * (G * ν) + G * ((4 / Real.sqrt a * m) * E) := by
        apply add_le_add (mul_le_mul_of_nonneg_right hA (mul_nonneg (Real.exp_pos _).le hν))
        exact mul_le_mul_of_nonneg_left hvb (Real.exp_pos _).le
      _ = (tailConstant a * ν + 4 / Real.sqrt a * m) * (E * G) := by ring
      _ ≤ _ := hmajor (by linarith)

private theorem signed_zero : nonholomorphicMode (shadowSign 0 : ℝ) 0 = fun _ => 0 := by
  funext z
  simp [nonholomorphicMode, modeAmplitude, shadowSign]

theorem differentiableAt_signedMode (m : ℕ) (z : ℂ) (hy : 0 < z.im) :
    DifferentiableAt ℝ (nonholomorphicMode (shadowSign m : ℝ) m) z := by
  by_cases hm : m = 0
  · subst m
    simp [signed_zero]
  · have hm' : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    have ha := hasDerivAt_modeAmplitude (shadowSign m : ℝ) m z.im hm' hy
    have hA := Complex.ofRealCLM.hasFDerivAt.comp z (ha.comp_hasFDerivAt z Complex.imCLM.hasFDerivAt)
    have hg : DifferentiableAt ℂ (fun w : ℂ =>
        Complex.exp (-((angularFrequency m : ℝ) : ℂ) * I * w)) z := by fun_prop
    exact hA.differentiableAt.mul (hg.restrictScalars ℝ)

private theorem majorant_zero_nonneg (a : ℝ) : 0 ≤ modeMajorant a 0 := by
  simp [modeMajorant, angularFrequency, tailConstant]
  positivity

theorem norm_signedMode_le (m : ℕ) (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : a ≤ z.im) :
    ‖nonholomorphicMode (shadowSign m : ℝ) m z‖ ≤ modeMajorant a m := by
  cases m with
  | zero => simpa [signed_zero] using majorant_zero_nonneg a
  | succ m => exact (bounds_pos a ha z hz _ m.succ_pos).1

theorem norm_fderiv_signedMode_le (m : ℕ) (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : a ≤ z.im) :
    ‖fderiv ℝ (nonholomorphicMode (shadowSign m : ℝ) m) z‖ ≤ modeMajorant a m := by
  cases m with
  | zero => simpa [signed_zero] using majorant_zero_nonneg a
  | succ m => exact (bounds_pos a ha z hz _ m.succ_pos).2

end MockThetaAnalytic
