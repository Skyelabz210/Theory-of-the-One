import FKTYTheta
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd

/-! The unary theta series in the FKTY period is a shifted Jacobi derivative.
In the variable τ = 3u the matrix sends the dual argument −1/τ to −1/τ−8,
an exact period of the untwisted derivative after Poisson summation. -/

noncomputable section

namespace MockThetaAnalytic

open Complex HurwitzZeta

private theorem shifted_hasSum (z τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => ((n : ℂ) + z) * exp (Real.pi * I * ((n : ℂ) + z)^2 * τ))
      (jacobiTheta₂'' z τ) := by
  have h := (((hasSum_jacobiTheta₂'_term (z*τ) hτ).div_const (2 * Real.pi * I)).add
    ((hasSum_jacobiTheta₂_term (z*τ) hτ).mul_left z)).mul_left (exp (Real.pi * I * z^2 * τ))
  apply h.congr_fun
  intro n
  rw [jacobiTheta₂'_term, mul_assoc (2 * (Real.pi : ℂ) * I), mul_div_cancel_left₀ _ two_pi_I_ne_zero,
    ← add_mul, mul_left_comm, jacobiTheta₂_term, ← Complex.exp_add]
  congr 2
  ring

private def positiveClass (u : ℂ) (n : ℤ) : ℂ :=
  if n % 6 = 1 then n * exp (2 * Real.pi * I * (n : ℂ)^2 * u / 24) else 0

private theorem split_classes (u : ℂ) (n : ℤ) :
    fktyThetaTerm u n = positiveClass u n + positiveClass u (-n) := by
  rw [fktyThetaTerm_eq_exp]
  unfold positiveClass fktyChi12
  simp only [Int.cast_neg, neg_sq, neg_one_zpow_eq_ite, Int.even_iff]
  split_ifs <;> first | omega | (push_cast; ring)

private theorem positiveClass_hasSum (u : ℂ) (hu : 0 < u.im) :
    HasSum (positiveClass u) (6 * jacobiTheta₂'' (1/6) (3*u)) := by
  let j : ℤ → ℤ := fun k => 6*k+1
  have hj : Function.Injective j := fun a b h => by dsimp [j] at h; omega
  apply (hj.hasSum_iff (f := positiveClass u) (fun n hn => ?_)).mp
  · have hs := (shifted_hasSum (1/6) (3*u) (by simpa using (show 0 < 3*u.im by positivity))).mul_left 6
    apply hs.congr_fun
    intro k
    change positiveClass u (6*k+1) = _
    simp only [positiveClass, show (6*k+1)%6 = 1 by omega, if_true]
    push_cast
    rw [show (2 * (Real.pi : ℂ) * I * (6*(k:ℂ)+1)^2 * u / 24) =
        Real.pi * I * ((k : ℂ) + 1 / 6)^2 * (3 * u) by ring]
    ring
  · unfold positiveClass
    apply if_neg
    intro hc
    exact hn ⟨n / 6, by dsimp [j]; omega⟩

/-- The FKTY theta equals twelve times the shifted Jacobi derivative with
characteristic 1/6. The two nonzero residue classes contribute equally. -/
theorem fktyTheta_eq_shiftedJacobi (u : ℂ) (hu : 0 < u.im) :
    fktyTheta u = 12 * jacobiTheta₂'' (1/6) (3*u) := by
  have hp := positiveClass_hasSum u hu
  have hinj : Function.Injective (fun n : ℤ => -n) := neg_injective
  have hn : Summable (fun n : ℤ => positiveClass u (-n)) := hp.summable.comp_injective hinj
  have heq : (∑' n : ℤ, positiveClass u (-n)) = ∑' n : ℤ, positiveClass u n :=
    (Equiv.neg ℤ).tsum_eq (positiveClass u)
  rw [fktyTheta, funext (split_classes u), hp.summable.tsum_add hn, heq, hp.tsum_eq]
  ring

/-- Principal powers divide without a branch correction on the right half-plane. -/
private theorem right_div_cpow (x y s : ℂ) (hx : 0 < x.re) (hy : 0 < y.re) :
    (x/y)^s = x^s / y^s := by
  have nx : x ≠ 0 := fun e => by simp [e] at hx
  have ny : y ≠ 0 := fun e => by simp [e] at hy
  obtain ⟨hxl,hxr⟩ := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  obtain ⟨hyl,hyr⟩ := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  have harg : y.arg ≠ Real.pi := by linarith [Real.pi_pos]
  have hl : log (x/y) = log x - log y := by
    rw [div_eq_mul_inv, log_mul nx (inv_ne_zero ny), log_inv _ harg, sub_eq_add_neg]
    rw [arg_inv, if_neg harg]
    exact ⟨by linarith, by linarith⟩
  rw [cpow_def_of_ne_zero (div_ne_zero nx ny), cpow_def_of_ne_zero nx,
    cpow_def_of_ne_zero ny, hl, sub_mul, exp_sub]

private theorem im_pos_neg_recip (u : ℂ) (hu : 0 < u.im) : 0 < (-1/u).im := by
  have h : u ≠ 0 := fun e => by simp [e] at hu
  rw [neg_div, one_div, neg_im, inv_im, neg_div, neg_neg]
  exact div_pos hu (normSq_pos.mpr h)

private theorem shifted_transform (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂'' z (τ/(8*τ+1)) = (8*τ+1)^(3/2 : ℂ) * jacobiTheta₂'' z τ := by
  let w : ℂ := -1/τ
  have hw : 0 < w.im := im_pos_neg_recip τ hτ
  have hv : 0 < (w-8).im := by simpa using hw
  have nw : w ≠ 0 := fun e => by simp [e] at hw
  have nv : w-8 ≠ 0 := fun e => by simp [e] at hv
  have nt : τ ≠ 0 := fun e => by simp [e] at hτ
  have h8 : 8*τ+1 ≠ 0 := by
    intro e
    have h := congrArg Complex.im e
    simp at h
    linarith
  have W (v : ℂ) (vpos : 0 < v.im) :
      jacobiTheta₂'' z (-1/v) = (-I*v)^(3/2 : ℂ) / (-2 * Real.pi) * jacobiTheta₂' z v := by
    have hv0 : v ≠ 0 := fun e => by simp [e] at vpos
    have hp0 : (-I*v)^(3/2 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hv0))
    have hp : (-2*(Real.pi : ℂ)) ≠ 0 := by exact mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [jacobiTheta₂'_functional_equation' z v]
    field_simp
  have he : -1/(w-8) = τ/(8*τ+1) := by
    apply (div_eq_div_iff nv h8).mpr
    dsimp [w]
    field_simp
    ring
  have he' : -1/w = τ := by dsimp [w]; field_simp
  have per : jacobiTheta₂' z (w-8) = jacobiTheta₂' z w := by
    have hh (t : ℂ) : jacobiTheta₂' z t = jacobiTheta₂' z (t+2) := (jacobiTheta₂'_add_right z t).symm
    calc
      _ = jacobiTheta₂' z (w-6) := (hh _).trans (by congr 1; ring)
      _ = jacobiTheta₂' z (w-4) := (hh _).trans (by congr 1; ring)
      _ = jacobiTheta₂' z (w-2) := (hh _).trans (by congr 1; ring)
      _ = jacobiTheta₂' z w := (hh _).trans (by congr 1; ring)
  have hx : 0 < (-I*(w-8)).re := by simpa [neg_mul, I_mul_re] using hv
  have hy : 0 < (-I*w).re := by simpa [neg_mul, I_mul_re] using hw
  have ratio : (-I*(w-8))/(-I*w) = 8*τ+1 := by dsimp [w]; field_simp; ring
  have hscale := right_div_cpow (-I*(w-8)) (-I*w) (3/2) hx hy
  rw [ratio] at hscale
  have nz : (-I*w)^(3/2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) nw))
  have hW := W w hw
  rw [he'] at hW
  rw [← he, W _ hv, per, hW, hscale]
  field_simp

/-- Weight-3/2 transformation for the actual FKTY unary theta under
the matrix with rows (1,0) and (24,1), throughout the upper half-plane. -/
theorem fktyTheta_lower_unipotent (u : ℂ) (hu : 0 < u.im) :
    fktyTheta (u/(24*u+1)) = (24*u+1)^(3/2 : ℂ) * fktyTheta u := by
  have hn : 24*u+1 ≠ 0 := by
    intro e
    have h := congrArg Complex.im e
    simp at h
    linarith
  have hmap : 0 < (u/(24*u+1)).im := by
    rw [Complex.div_im]
    have hp : (24*u+1).normSq > 0 := normSq_pos.mpr hn
    rw [← sub_div]
    apply div_pos _ hp
    simp [Complex.mul_re, Complex.mul_im]
    linarith
  have h3 : 0 < (3*u).im := by simpa using (show 0 < 3*u.im by positivity)
  rw [fktyTheta_eq_shiftedJacobi _ hmap, fktyTheta_eq_shiftedJacobi _ hu]
  have ht := shifted_transform (1/6) (3*u) h3
  rw [show 8*(3*u)+1=24*u+1 by ring, show 3*u/(24*u+1) = 3*(u/(24*u+1)) by ring] at ht
  rw [ht]
  ring

end MockThetaAnalytic
