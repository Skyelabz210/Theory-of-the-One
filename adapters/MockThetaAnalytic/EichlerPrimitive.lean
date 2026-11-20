import FKTYPeriodRegularity
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! A primitive for the FKTY differential on the whole upper half-plane, and
bounds for comparing its values along paths approaching a rational cusp. -/

noncomputable section

namespace MockThetaAnalytic
open Complex Set Filter Metric MeasureTheory KElimination.ShadowConvergence
open scoped Topology

private def toDisk (z : ℂ) := (z-I)/(z+I)
private def fromDisk (w : ℂ) := I*(1+w)/(1-w)

private theorem upper_ne (z : ℂ) (hz : 0 < z.im) : z+I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

private theorem toDisk_mem (z : ℂ) (hz : 0 < z.im) : toDisk z ∈ ball 0 1 := by
  rw [mem_ball, dist_zero_right, toDisk, norm_div, div_lt_one (norm_pos_iff.mpr (upper_ne z hz))]
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
  simp [normSq_sub, normSq_add]
  linarith

private theorem fromDisk_ne {w : ℂ} (hw : w ∈ ball 0 1) : 1-w ≠ 0 := by
  intro h
  rw [← sub_eq_zero.mp h] at hw
  simp at hw

private theorem fromDisk_im {w : ℂ} (hw : w ∈ ball 0 1) : 0 < (fromDisk w).im := by
  have hw' : ‖w‖ < 1 := by simpa using hw
  have hs := sq_lt_sq₀ (norm_nonneg w) (by norm_num : (0:ℝ) ≤ 1) |>.2 hw'
  rw [← normSq_eq_norm_sq, normSq_apply] at hs
  simp only [fromDisk, div_im, mul_im, mul_re, one_re, one_im, I_re, I_im, add_im, add_re,
    sub_re, sub_im, zero_add, zero_sub, one_mul, zero_mul]
  have hn := normSq_pos.mpr (fromDisk_ne hw)
  field_simp
  nlinarith

/-- Transfer a disk primitive through the Cayley map. This gives one primitive
valid simultaneously on all the paths in the upper half-plane. -/
theorem isExactOn_upperHalf {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ f z) :
    IsExactOn f {z : ℂ | 0 < z.im} := by
  let pull (w : ℂ) := f (fromDisk w) * (2*I / (1-w)^2)
  have hex : DifferentiableOn ℂ pull (ball 0 1) := by
    intro w hw
    have hn := fromDisk_ne hw
    have hg : DifferentiableAt ℂ fromDisk w := by unfold fromDisk; fun_prop (disch := assumption)
    have hn2 := pow_ne_zero 2 hn
    exact (((hf _ (fromDisk_im hw)).comp w hg).mul (by fun_prop (disch := assumption))).differentiableWithinAt
  obtain ⟨F,hF⟩ := hex.isExactOn_ball
  refine ⟨F ∘ toDisk, ?_⟩
  intro z hz
  have hn := upper_ne z hz
  have hc : HasDerivAt toDisk (2*I/(z+I)^2) z := by
    convert ((hasDerivAt_id z).sub_const I).div ((hasDerivAt_id z).add_const I) hn using 1
    simp
    ring
  have hinv : fromDisk (toDisk z) = z := by
    unfold fromDisk toDisk
    field_simp
    ring_nf
  have h := (hF _ (toDisk_mem z hz)).comp z hc
  convert h using 1
  dsimp only [pull]
  rw [hinv]
  have hne := fromDisk_ne (toDisk_mem z hz)
  unfold toDisk at *
  field_simp
  ring

private theorem differentiableAt_shadowSeries (u : ℂ) (hu : ‖u‖ < 1) :
    DifferentiableAt ℂ shadowSeries u := by
  obtain ⟨r, hur, hr⟩ := exists_between hu
  have hpos : 0 ≤ r := (norm_nonneg _).trans hur.le
  have hs : Summable (fun m : ℕ => (m : ℝ)*r^m) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one
      (r := r) 1 (by simpa only [Real.norm_eq_abs, abs_of_nonneg hpos] using hr)
  have hop : IsOpen {w : ℂ | ‖w‖ < r} := isOpen_lt continuous_norm continuous_const
  have hadd := Complex.differentiableOn_tsum_of_summable_norm (F := fun m w => shadowTerm w m)
    hs (fun m w _ => by unfold shadowTerm; fun_prop) hop (fun m w hw =>
      (norm_shadowTerm_le w (le_trans (le_of_lt hw) hr.le) m).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) (le_of_lt hw) _) (by positivity)))
  exact hadd.differentiableAt (hop.mem_nhds hur)

/-- The numerator is holomorphic everywhere above the real axis. -/
theorem differentiableAt_fktyTheta (z : ℂ) (hz : 0 < z.im) : DifferentiableAt ℂ fktyTheta z := by
  have h := (differentiableAt_shadowSeries _ (norm_shadowNome_lt_one z hz)).comp z
    (show DifferentiableAt ℂ shadowNome z by unfold shadowNome; fun_prop)
  apply (h.const_mul 2).congr_of_eventuallyEq
  filter_upwards [continuous_im.continuousAt (Ioi_mem_nhds hz)] with w hw
  exact fktyTheta_eq_shadowSeries w hw

/-- The holomorphic differential whose vertical integrals yield the period. -/
def eichlerForm (x : ℝ) (z : ℂ) := fktyTheta z / ((z-(x : ℂ)) ^ (1/2 : ℂ))

theorem exists_eichlerPrimitive (x : ℝ) :
    ∃ F : ℂ → ℂ, ∀ z : ℂ, 0 < z.im → HasDerivAt F (eichlerForm x z) z := by
  apply isExactOn_upperHalf
  intro z hz
  have hs : z-(x:ℂ) ∈ slitPlane := mem_slitPlane_iff.mpr (.inr (by simpa using hz.ne'))
  exact (differentiableAt_fktyTheta z hz).div
    (((differentiableAt_id.sub_const _).cpow_const hs))
    (cpow_ne_zero_iff.mpr (.inl (slitPlane_ne_zero hs)))

/-- Parameterizing a vertical line multiplies the differential by i. -/
theorem hasDerivAt_eichlerPrimitive_vertical (x c t : ℝ) (ht : 0 < t) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (eichlerForm x z) z) :
    HasDerivAt (fun v : ℝ => F ((c : ℂ) + (v : ℂ)*I))
      (I * eichlerForm x ((c : ℂ)+(t : ℂ)*I)) t := by
  have h := hF ((c : ℂ)+(t : ℂ)*I) (by simpa using ht)
  have hc := h.comp (t : ℂ) (((hasDerivAt_id (t : ℂ)).mul_const I).const_add (c : ℂ))
  simpa only [id_eq, one_mul, Function.comp_apply, mul_comm I] using hc.comp_ofReal

end MockThetaAnalytic
