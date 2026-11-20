import FKTYTheta
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A uniform positive-height bound on the unary theta kernel and the cost of
moving between two vertical approaches at a common height. -/

noncomputable section
namespace MockThetaAnalytic
open Complex Set Filter KElimination.ShadowConvergence KElimination.MockThetaShadow
open scoped Topology

private theorem gaussianStep (b : ℝ) (hb : 0 < b) (n : ℕ) :
    ((n : ℝ)+1)*Real.exp (-b*((n : ℝ)+1)^2) ≤
      (Real.exp (-b*(n : ℝ)^2) - Real.exp (-b*((n : ℝ)+1)^2))/b := by
  let x : ℝ := n
  change (x+1)*_ ≤ (_ - _)/b
  have hx : 0 ≤ x := Nat.cast_nonneg _
  have h := Real.add_one_le_exp (b*(2*x+1))
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (-b*(x+1)^2)).le
  rw [← Real.exp_add, show b*(2*x+1)+(-b*(x+1)^2) = -b*x^2 by ring] at h'
  apply (le_div_iff₀ hb).2
  change (x+1)*Real.exp (-b*(x+1)^2)*b ≤ _
  nlinarith [mul_nonneg (mul_nonneg hb.le hx) (Real.exp_pos (-b*(x+1)^2)).le]

private theorem gaussianPartial (b : ℝ) (hb : 0 < b) (N : ℕ) :
    (∑ m ∈ Finset.range (N+1), (m : ℝ)*Real.exp (-b*(m : ℝ)^2)) ≤
      (1-Real.exp (-b*(N : ℝ)^2))/b := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    exact (add_le_add ih (gaussianStep b hb n)).trans_eq (by ring)

/-- The estimate is uniform in the real part. The factor two is from the
positive- and negative-frequency pairing of the bilateral FKTY series. -/
theorem norm_fktyTheta_le_height (z : ℂ) (hz : 0 < z.im) :
    ‖fktyTheta z‖ ≤ (24/Real.pi) / z.im := by
  let b := (Real.pi/12)*z.im
  have hb : 0 < b := by dsimp [b]; positivity
  have hn : ‖shadowNome z‖ = Real.exp (-b) := by
    rw [shadowNome, Complex.norm_exp, Complex.mul_I_re]
    congr 1
    simp [Complex.mul_im, b]
    ring_nf
    simp
  have hbound (m : ℕ) : ‖shadowTerm (shadowNome z) m‖ ≤
      (m : ℝ) * Real.exp (-b*(m : ℝ)^2) := by
    have hw : ((shadowWeight m).natAbs : ℝ) ≤ m := by exact_mod_cast shadowWeight_natAbs_le m
    rw [Nat.cast_natAbs, Int.cast_abs] at hw
    rw [shadowTerm, norm_mul, norm_pow, Complex.norm_intCast, hn, ← Real.exp_nat_mul]
    push_cast
    rw [mul_comm ((m : ℝ)^2) (-b)]
    exact mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
  have hs := norm_shadowTerm_summable _ (norm_shadowNome_lt_one z hz)
  have hle : (∑' m, ‖shadowTerm (shadowNome z) m‖) ≤ 1/b := by
    apply le_of_tendsto_of_tendsto' hs.hasSum.tendsto_sum_nat tendsto_const_nhds
    intro n
    cases n with
    | zero => simp [le_of_lt hb]
    | succ n =>
      exact (Finset.sum_le_sum fun i _ => hbound i).trans ((gaussianPartial b hb n).trans
        (div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) hb.le))
  rw [fktyTheta_eq_shadowSeries z hz, norm_mul, Complex.norm_ofNat, shadowSeries]
  calc
    _ ≤ 2 * (1/b) := by gcongr; exact (norm_tsum_le_tsum_norm hs).trans hle
    _ = _ := by dsimp [b]; ring

/-- A primitive of the Eichler differential changes by at most this quantity
along any horizontal segment at height h. -/
theorem norm_horizontal_bridge_le (x c c' h : ℝ) (hh : 0 < h) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F
      (fktyTheta z / ((z-(x : ℂ))^(1/2 : ℂ))) z) :
    ‖F ((c' : ℂ) + (h : ℂ)*I) - F ((c : ℂ) + (h : ℂ)*I)‖ ≤
      (24/Real.pi) * |c'-c| / (h * Real.sqrt h) := by
  let z (v : ℝ) : ℂ := (v : ℂ) + (h : ℂ)*I
  let deriv (v : ℝ) := fktyTheta (z v) / ((z v - (x : ℂ))^(1/2 : ℂ))
  have him (v : ℝ) : (z v).im = h := by simp [z]
  have hd (v : ℝ) : HasDerivAt (fun u : ℝ => F (z u)) (deriv v) v := by
    simpa [Function.comp_def, z, deriv] using ((hF _ ((him v).symm ▸ hh)).comp (v : ℂ)
      ((hasDerivAt_id (v : ℂ)).add_const ((h : ℂ)*I))).comp_ofReal
  have hb (v : ℝ) : ‖deriv v‖ ≤ (24/Real.pi)/(h * Real.sqrt h) := by
    have h1 := norm_fktyTheta_le_height (z v) ((him v).symm ▸ hh)
    rw [him] at h1
    have h2 : h ≤ ‖z v-(x : ℂ)‖ := by
      simpa [z, abs_of_pos hh] using abs_im_le_norm (z v - (x : ℂ))
    have eq : ‖(z v-(x : ℂ))^(1/2 : ℂ)‖ = Real.sqrt ‖z v-(x : ℂ)‖ := by
      simpa [Real.sqrt_eq_rpow] using norm_cpow_real (z v - (x : ℂ)) (1/2)
    dsimp only [deriv]
    rw [norm_div, eq, ← div_div]
    exact div_le_div₀ (by positivity) h1 (Real.sqrt_pos.2 hh) (Real.sqrt_le_sqrt h2)
  have res := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v _ => (hd v).hasDerivWithinAt) (fun v _ => hb v) (mem_univ c) (mem_univ c')
  calc
    _ ≤ _ := res
    _ = _ := by rw [Real.norm_eq_abs]; ring

end MockThetaAnalytic
