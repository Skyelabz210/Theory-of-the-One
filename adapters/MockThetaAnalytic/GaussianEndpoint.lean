import GaussianPairIntegrable
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Gaussian modes with the square-root singularity of the Eichler kernel.
Second differences have summable integrals in the frequency index. -/

noncomputable section
namespace MockThetaAnalytic
open MeasureTheory Set

def rootedGaussian (a : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  gaussianMode a m t / Real.sqrt t

private def moment (b : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (b*t)^k * Real.exp (-(b*t)) / Real.sqrt t

private theorem moment_eq (b : ℝ) (hb : 0 < b) (k : ℕ) (t : ℝ) (ht : 0 < t) :
    moment b k t = Real.sqrt b * (Real.exp (-(b*t)) * (b*t)^((k:ℝ)+1/2-1)) := by
  rw [show (k:ℝ)+1/2-1 = (k:ℝ)-1/2 by ring, Real.rpow_sub (mul_pos hb ht),
    Real.rpow_natCast, ← Real.sqrt_eq_rpow, Real.sqrt_mul hb.le]
  unfold moment
  field_simp [(Real.sqrt_pos.2 hb).ne', (Real.sqrt_pos.2 ht).ne']

private theorem integrableOn_moment (b : ℝ) (hb : 0 < b) (k : ℕ) :
    IntegrableOn (moment b k) (Ioi 0) := by
  let g (t : ℝ) := Real.exp (-t) * t^((k:ℝ)+1/2-1)
  have h : IntegrableOn g (Ioi 0) := Real.GammaIntegral_convergent (by positivity)
  have hs : IntegrableOn (fun t => g (b*t)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff g 0 hb).2 (by simpa only [mul_zero] using h)
  exact (IntegrableOn.congr_fun (hs.const_mul (Real.sqrt b))
    (fun t ht => (moment_eq b hb k t ht).symm) measurableSet_Ioi)

private theorem integral_moment (b : ℝ) (hb : 0 < b) (k : ℕ) :
    (∫ t in Ioi 0, moment b k t) = Real.Gamma ((k:ℝ)+1/2) / Real.sqrt b := by
  let g (t : ℝ) := Real.exp (-t) * t^((k:ℝ)+1/2-1)
  calc
    _ = ∫ t in Ioi (0:ℝ), Real.sqrt b * g (b*t) :=
      setIntegral_congr_fun measurableSet_Ioi (moment_eq b hb k)
    _ = _ := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 hb, mul_zero, smul_eq_mul,
        ← Real.Gamma_eq_integral (show 0 < (k:ℝ)+1/2 by positivity)]
      field_simp [(Real.sqrt_pos.2 hb).ne']
      rw [Real.sq_sqrt hb.le]

theorem integrableOn_rootedGaussian (a : ℝ) (ha : 0 < a) (m : ℕ) :
    IntegrableOn (rootedGaussian a m) (Ioi 0) := by
  by_cases hm : m = 0
  · have hz : rootedGaussian a 0 = fun _ => 0 := by
      funext t
      simp [rootedGaussian, gaussianMode]
    rw [hm, hz]
    exact integrableOn_zero
  have hm' : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hb : 0 < a*(m:ℝ)^2 := mul_pos ha (sq_pos_of_pos hm')
  have he : rootedGaussian a m = fun t => (m:ℝ) * moment (a*(m:ℝ)^2) 0 t := by
    funext t
    simp only [rootedGaussian, gaussianMode, moment, pow_zero, one_mul]
    rw [mul_div_assoc, neg_mul]
  rw [he]
  exact (integrableOn_moment _ hb 0).const_mul _

theorem integral_rootedGaussian (a : ℝ) (ha : 0 < a) (m : ℕ) (hm : 0 < m) :
    (∫ t in Ioi 0, rootedGaussian a m t) = Real.sqrt Real.pi / Real.sqrt a := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  calc
    _ = ∫ t in Ioi (0:ℝ), (m:ℝ) * moment (a*(m:ℝ)^2) 0 t := by
      congr 1
      ext t
      simp only [rootedGaussian, gaussianMode, moment, pow_zero, one_mul]
      rw [mul_div_assoc, neg_mul]
    _ = _ := by
      rw [integral_const_mul, integral_moment _ (mul_pos ha (sq_pos_of_pos hm')), Nat.cast_zero,
        zero_add, Real.Gamma_one_half_eq, Real.sqrt_mul ha.le, Real.sqrt_sq hm'.le]
      field_simp [(Real.sqrt_pos.2 ha).ne', hm'.ne']

private theorem gamma_three_halves :
    Real.Gamma (3/2) = Real.sqrt Real.pi / 2 := by
  rw [show (3/2:ℝ) = 1/2+1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

private theorem gamma_five_halves :
    Real.Gamma (5/2) = 3 * Real.sqrt Real.pi / 4 := by
  rw [show (5/2:ℝ) = 3/2+1 by norm_num, Real.Gamma_add_one (by norm_num), gamma_three_halves]
  ring

private theorem gaussian_difference_bounds (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t)
    (m S : ℕ) (hm : 0 < m) (hS : S ≤ m) :
    let z := a*(m:ℝ)^2*t
    ‖gaussianMode a m t - gaussianMode a (m+S) t‖ ≤ S*(1+3*z)*Real.exp (-z) ∧
    ‖gaussianMode a m t - 2*gaussianMode a (m+S) t + gaussianMode a (m+2*S) t‖ ≤
      ((S:ℝ)^2/m)*(12*z+9*z^2)*Real.exp (-z) := by
  let x : ℝ := m
  let d : ℝ := S
  let z := a*x^2*t
  let p := a*(2*x*d+d^2)*t
  let q := 2*a*d^2*t
  let E := Real.exp (-z)
  let u := Real.exp (-p)
  let v := Real.exp (-q)
  have hx : 0 < x := by dsimp [x]; exact_mod_cast hm
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hdx : d ≤ x := by dsimp [d, x]; exact_mod_cast hS
  have hP : 0 ≤ p := by dsimp [p]; positivity
  have hQ : 0 ≤ q := by dsimp [q]; positivity
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hu0 : 0 ≤ u := (Real.exp_pos _).le
  have hu1 : u ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hP)
  have hv1 : v ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hQ)
  have hu : 0 ≤ 1-u := sub_nonneg.mpr hu1
  have hv : 0 ≤ 1-v := sub_nonneg.mpr hv1
  have hp : 1-u ≤ p := by dsimp [u]; linarith [Real.add_one_le_exp (-p)]
  have hq : 1-v ≤ q := by dsimp [v]; linarith [Real.add_one_le_exp (-q)]
  have hpm : p ≤ 3*a*x*d*t := by
    have hd2 : d^2 ≤ x*d := by simpa only [pow_two] using mul_le_mul_of_nonneg_right hdx hd
    dsimp [p]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (show 2*x*d+d^2 ≤ 3*x*d by linarith) ha.le) ht).trans_eq (by ring)
  have h0 : gaussianMode a m t = x*E := by
    simp only [gaussianMode, x, E, z, neg_mul]
  have h1 : gaussianMode a (m+S) t = (x+d)*(E*u) := by
    unfold gaussianMode
    push_cast
    rw [← Real.exp_add]
    dsimp [x, d, E, u, z, p]
    ring_nf
  have h2 : gaussianMode a (m+2*S) t = (x+2*d)*(E*u*u*v) := by
    unfold gaussianMode
    push_cast
    simp only [← Real.exp_add, E, u, v]
    dsimp [x,d,z,p,q]
    ring_nf
  rw [h0, h1, h2]
  change ‖x*E-(x+d)*(E*u)‖ ≤ d*(1+3*z)*E ∧
    ‖x*E-2*((x+d)*(E*u))+(x+2*d)*(E*u*u*v)‖ ≤ (d^2/x)*(12*z+9*z^2)*E
  constructor
  · rw [show x*E-(x+d)*(E*u) = E*(x*(1-u)-d*u) by ring,
      norm_mul, Real.norm_of_nonneg hE, Real.norm_eq_abs]
    have ha' : 0 ≤ x*(1-u) := mul_nonneg hx.le hu
    have hb' : 0 ≤ d*u := mul_nonneg hd hu0
    calc
      _ ≤ E*(x*(1-u)+d*u) := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) hE
      _ ≤ E*(x*(3*a*x*d*t)+d*1) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (hp.trans hpm) hx.le)
          (mul_le_mul_of_nonneg_left hu1 hd)) hE
      _ = _ := by dsimp [z]; ring
  · rw [show x*E-2*((x+d)*(E*u))+(x+2*d)*(E*u*u*v) =
        E*(x*(1-u)^2-2*d*u*(1-u)-(x+2*d)*u^2*(1-v)) by ring,
      norm_mul, Real.norm_of_nonneg hE, Real.norm_eq_abs]
    have ha' : 0 ≤ x*(1-u)^2 := by positivity
    have hb' : 0 ≤ 2*d*u*(1-u) := by positivity
    have hc' : 0 ≤ (x+2*d)*u^2*(1-v) := by positivity
    have h₁ : x*(1-u)^2 ≤ x*(3*a*x*d*t)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu (hp.trans hpm) 2) hx.le
    have h₂ : 2*d*u*(1-u) ≤ 2*d*1*(3*a*x*d*t) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hu1 (by positivity)) (hp.trans hpm) hu (by positivity)
    have hu2 : u^2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hu0 hu1 2
    have h₃ : (x+2*d)*u^2*(1-v) ≤ (3*x)*1*q :=
      mul_le_mul (mul_le_mul (by linarith) hu2 (sq_nonneg _) (by positivity)) hq hv (by positivity)
    calc
      _ ≤ E*(x*(1-u)^2+2*d*u*(1-u)+(x+2*d)*u^2*(1-v)) :=
        mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) hE
      _ ≤ E*(x*(3*a*x*d*t)^2+2*d*1*(3*a*x*d*t)+(3*x)*1*q) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add h₁ h₂) h₃) hE
      _ = _ := by dsimp [z,q]; field_simp [hx.ne']; ring

theorem integral_rootedGaussian_sub_le (a : ℝ) (ha : 0 < a) (m S : ℕ)
    (hm : 0 < m) (hS : S ≤ m) :
    (∫ t in Ioi 0, ‖rootedGaussian a m t - rootedGaussian a (m+S) t‖) ≤
      (Real.sqrt Real.pi / Real.sqrt a) * (5/2) * S/m := by
  let b := a*(m:ℝ)^2
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hb : 0 < b := mul_pos ha (sq_pos_of_pos hm')
  have hI k := integrableOn_moment b hb k
  have hG j := integrableOn_rootedGaussian a ha j
  have hmajor : IntegrableOn (fun t => (S:ℝ)*(moment b 0 t+3*moment b 1 t)) (Ioi 0) :=
    ((hI 0).add ((hI 1).const_mul 3)).const_mul _
  calc
    _ ≤ ∫ t in Ioi (0:ℝ), (S:ℝ)*(moment b 0 t+3*moment b 1 t) := by
      apply integral_mono_ae ((hG m).sub (hG (m+S))).norm hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have he := (gaussian_difference_bounds a t ha (mem_Ioi.mp ht).le m S hm hS).1
      change ‖rootedGaussian a m t - rootedGaussian a (m+S) t‖ ≤ _
      simp only [rootedGaussian, ← sub_div, norm_div, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      refine (div_le_div_of_nonneg_right he (Real.sqrt_nonneg _)).trans_eq ?_
      simp only [moment, pow_zero, pow_one, one_mul, b]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_add (hI 0) ((hI 1).const_mul 3), integral_const_mul,
        integral_moment _ hb, integral_moment _ hb]
      norm_num only [Nat.cast_zero, Nat.cast_one, zero_add, Real.Gamma_one_half_eq]
      rw [gamma_three_halves]
      simp only [b, Real.sqrt_mul ha.le, Real.sqrt_sq hm'.le]
      ring

theorem integral_rootedGaussian_second_sub_le (a : ℝ) (ha : 0 < a) (m S : ℕ)
    (hm : 0 < m) (hS : S ≤ m) :
    (∫ t in Ioi 0, ‖rootedGaussian a m t - 2*rootedGaussian a (m+S) t +
      rootedGaussian a (m+2*S) t‖) ≤
      (Real.sqrt Real.pi / Real.sqrt a) * (51/4) * ((S:ℝ)/m)^2 := by
  let b := a*(m:ℝ)^2
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hb : 0 < b := mul_pos ha (sq_pos_of_pos hm')
  have hI k := integrableOn_moment b hb k
  have hG j := integrableOn_rootedGaussian a ha j
  have hmajor : IntegrableOn (fun t => ((S:ℝ)^2/m)*(12*moment b 1 t+9*moment b 2 t)) (Ioi 0) :=
    (((hI 1).const_mul 12).add ((hI 2).const_mul 9)).const_mul _
  calc
    _ ≤ ∫ t in Ioi (0:ℝ), ((S:ℝ)^2/m)*(12*moment b 1 t+9*moment b 2 t) := by
      apply integral_mono_ae (((hG m).sub ((hG (m+S)).const_mul 2)).add (hG (m+2*S))).norm hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have he := (gaussian_difference_bounds a t ha (mem_Ioi.mp ht).le m S hm hS).2
      change ‖rootedGaussian a m t - 2*rootedGaussian a (m+S) t + rootedGaussian a (m+2*S) t‖ ≤ _
      simp only [rootedGaussian, ← mul_div_assoc, ← sub_div, ← add_div, norm_div,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      refine (div_le_div_of_nonneg_right he (Real.sqrt_nonneg _)).trans_eq ?_
      simp only [moment, pow_one, b]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_add ((hI 1).const_mul 12) ((hI 2).const_mul 9),
        integral_const_mul, integral_const_mul, integral_moment _ hb, integral_moment _ hb]
      norm_num only [Nat.cast_one, Nat.cast_ofNat]
      rw [gamma_three_halves, gamma_five_halves]
      simp only [b, Real.sqrt_mul ha.le, Real.sqrt_sq hm'.le]
      ring

end MockThetaAnalytic
