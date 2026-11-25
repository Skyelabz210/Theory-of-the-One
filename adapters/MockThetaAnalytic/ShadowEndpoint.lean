import ShadowPeriod
import GaussianEndpoint
import EichlerCuspLimit

/-! Two cutoffs separated by an antiperiod of the cusp phase. Their average
removes the boundary oscillation, allowing the parameter to equal the cusp. -/

noncomputable section
namespace MockThetaAnalytic.ShadowEndpoint

open Complex Filter MeasureTheory Set ShadowReadings ShadowHecke ShadowPeriod
open KElimination.MockTheta KElimination.MockThetaShadow
open scoped BigOperators Topology

private def s : ℝ := -1/24
private def kernel (x t : ℝ) : ℂ := fktyVerticalKernel s x t
private def scale : ℝ := Real.sqrt Real.pi / Real.sqrt gaussianRate
private def v (w : Phase → ℂ) (m : ℕ) : ℂ := w (phase m) * fktyCuspPhase m

/-- The first N frequency slots of the one observed prefix. -/
def periodUpTo {D : ℕ} (reading : Prefix D) (w : Phase → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0:ℝ), kernel x t * recoveredThetaUpTo reading w N (cuspRay t)

/-- Average the largest available cutoff and the cutoff one shift before it. -/
def averagedPeriod {D : ℕ} (reading : Prefix D) (w : Phase → ℂ) (S : ℕ) (x : ℝ) : ℂ :=
  (periodUpTo reading w (modeCount D-S) x + periodUpTo reading w (modeCount D) x) / 2

theorem periodUpTo_all {D : ℕ} (reading : Prefix D) (w : Phase → ℂ) (x : ℝ) :
    periodUpTo reading w (modeCount D) x = recoveredPeriod reading w x := rfl

private theorem rate_pos : 0 < gaussianRate := by unfold gaussianRate; positivity

/-- The distance to the real parameter is at least the height for every x. -/
theorem norm_kernel_le_height (x t : ℝ) (ht : 0 < t) :
    ‖fktyVerticalKernel (-1/24) x t‖ ≤ 1 / Real.sqrt t := by
  let z : ℂ := ((-1/24 : ℝ) : ℂ) + (t : ℂ)*I - (x : ℂ)
  have hz : t ≤ ‖z‖ := by simpa [z, abs_of_pos ht] using abs_im_le_norm z
  have hn : ‖z ^ (1/2 : ℂ)‖ = Real.sqrt ‖z‖ := by
    simpa [Real.sqrt_eq_rpow] using norm_cpow_real z (1/2)
  change ‖I / (z^(1/2:ℂ))‖ ≤ _
  rw [norm_div, norm_I, hn]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 ht) (Real.sqrt_le_sqrt hz)

private theorem kernel_mul_le (x t : ℝ) (ht : 0 < t) (c : ℂ) (g : ℝ) :
    ‖kernel x t * (c * (g : ℂ))‖ ≤ ‖c‖ * ‖g / Real.sqrt t‖ := by
  simp only [norm_mul, Complex.norm_real, norm_div, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (1 / Real.sqrt t) * (‖c‖ * ‖g‖) :=
      mul_le_mul_of_nonneg_right (norm_kernel_le_height x t ht) (by positivity)
    _ = _ := by ring

private theorem kernel_mul_integrable (x : ℝ) (c : ℂ) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioi 0)) (hg' : IntegrableOn (fun t => g t / Real.sqrt t) (Ioi 0)) :
    IntegrableOn (fun t => kernel x t * (c * (g t : ℂ))) (Ioi 0) := by
  apply (hg'.norm.const_mul ‖c‖).mono'
    (((continuousOn_fktyVerticalKernel s x).aestronglyMeasurable measurableSet_Ioi).mul (hg.ofReal.const_mul c).1)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact kernel_mul_le x t ht c (g t)

private theorem integral_norm_kernel_mul_le (x : ℝ) {c : ℂ} (hc : ‖c‖ ≤ 1) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioi 0)) (hg' : IntegrableOn (fun t => g t / Real.sqrt t) (Ioi 0)) :
    (∫ t in Ioi (0:ℝ), ‖kernel x t * (c * (g t : ℂ))‖) ≤
      ∫ t in Ioi (0:ℝ), ‖g t / Real.sqrt t‖ := by
  apply integral_mono_ae (kernel_mul_integrable x c hg hg').norm hg'.norm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (kernel_mul_le x t ht c (g t)).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (g t / Real.sqrt t)))

private theorem mode_integrable (x : ℝ) (w : Phase → ℂ) (m : ℕ) :
    IntegrableOn (fun t => kernel x t * (v w m * (gaussianMode gaussianRate m t : ℂ))) (Ioi 0) :=
  kernel_mul_integrable x _ (integrableOn_gaussianMode _ rate_pos m)
    (integrableOn_rootedGaussian _ rate_pos m)

private theorem polynomial_integrable (D N : ℕ) (w : Phase → ℂ) (x : ℝ) (hN : N ≤ modeCount D) :
    IntegrableOn (fun t => kernel x t * recoveredThetaUpTo (observe D mockCoeff) w N (cuspRay t))
      (Ioi 0) := by
  have h : IntegrableOn (fun t => ∑ m ∈ Finset.range N,
      kernel x t * (v w m * (gaussianMode gaussianRate m t : ℂ))) (Ioi 0) :=
    integrable_finset_sum _ (fun m _ => mode_integrable x w m)
  refine (h.const_mul (2:ℂ)).congr (Eventually.of_forall fun t => ?_)
  change 2 * (∑ m ∈ Finset.range N,
      kernel x t * (v w m * (gaussianMode gaussianRate m t : ℂ))) =
    kernel x t * recoveredThetaUpTo (observe D mockCoeff) w N (cuspRay t)
  rw [recoveredThetaUpTo_ray D N w t hN]
  simp only [v, ← Finset.mul_sum]
  ring

private theorem shifted_summable {f : ℕ → ℂ} (hf : Summable f) (N : ℕ) :
    Summable (fun j => f (N+j)) := by
  simpa only [Nat.add_comm N] using (summable_nat_add_iff N).2 hf

private theorem sum_with_shift {f : ℕ → ℂ} (hf : Summable f) (N : ℕ) :
    (∑ m ∈ Finset.range N, f m) + (∑' j : ℕ, f (N+j)) = ∑' m, f m := by
  simpa only [Nat.add_comm N] using hf.sum_add_tsum_nat_add N

private theorem gaussian_average_tail (S N : ℕ) (w : Phase → ℂ)
    (ha : ∀ m, v w (m+S) = -v w m) (hw : ∀ r, ‖w r‖ ≤ 1) (t : ℝ) (ht : 0 < t) :
    let g (m : ℕ) : ℝ := gaussianMode gaussianRate m t
    let f (m : ℕ) : ℂ := v w m * (g m : ℂ)
    2 * (weightedCuspTheta w t - ((∑ m ∈ Finset.range N, f m) +
      (∑ m ∈ Finset.range (N+S), f m))) =
      (∑ j ∈ Finset.range S, v w (N+j) * ((g (N+j) - g (N+j+S) : ℝ) : ℂ)) +
      ∑' j : ℕ, v w (N+j) *
        ((g (N+j) - 2*g (N+j+S) + g (N+j+2*S) : ℝ) : ℂ) := by
  dsimp only
  let f (m : ℕ) := v w m * (gaussianMode gaussianRate m t : ℂ)
  let p (j : ℕ) := f (N+j) + f (N+j+S)
  have hf : Summable f := weightedModes_summable w hw t ht
  have hfN := shifted_summable hf N
  have hfNS : Summable (fun j => f (N+j+S)) := by
    simpa only [Nat.add_right_comm] using shifted_summable hf (N+S)
  have hp : Summable p := hfN.add hfNS
  have hfirst (j : ℕ) : v w (N+j) *
      ((gaussianMode gaussianRate (N+j) t - gaussianMode gaussianRate (N+j+S) t : ℝ) : ℂ) = p j := by
    simp only [p, f, ha, ofReal_sub]
    ring
  have hsecond (j : ℕ) : v w (N+j) *
      ((gaussianMode gaussianRate (N+j) t - 2*gaussianMode gaussianRate (N+j+S) t +
        gaussianMode gaussianRate (N+j+2*S) t : ℝ) : ℂ) = p j + p (j+S) := by
    simp only [p, f, ← Nat.add_assoc, ha, ofReal_sub, ofReal_add, ofReal_mul, ofReal_ofNat]
    have h : N+j+2*S = N+j+S+S := by omega
    rw [h]
    simp only [neg_neg]
    ring
  simp_rw [hfirst, hsecond]
  rw [hp.tsum_add ((summable_nat_add_iff S).2 hp)]
  have hN := sum_with_shift hf N
  have hNS := sum_with_shift hf (N+S)
  have hpsum := hfN.tsum_add hfNS
  have hshift := hp.sum_add_tsum_nat_add S
  simp only [weightedCuspTheta, ← mul_assoc (w _)]
  change 2 * (2 * ∑' m, f m - ((∑ m ∈ Finset.range N, f m) +
    ∑ m ∈ Finset.range (N+S), f m)) =
      (∑ j ∈ Finset.range S, p j) + ((∑' j, p j) + ∑' j : ℕ, p (j+S))
  simp only [Nat.add_right_comm N S] at hNS
  linear_combination -2*hN - 2*hNS - 2*hpsum - hshift

/-- A bound for the two-cutoff average at every real parameter, including s. -/
private theorem averagedPeriod_control_of_shift (D S : ℕ) (w : Phase → ℂ)
    (hw : ∀ r, ‖w r‖ ≤ 1) (ha : ∀ m, v w (m+S) = -v w m)
    (hN : max 2 S ≤ modeCount D-S) (x : ℝ) :
    IntegrableOn (fun t => kernel x t * weightedCuspTheta w t) (Ioi 0) ∧
    ‖averagedPeriod (observe D mockCoeff) w S x - weightedCuspPeriod w x‖ ≤
      8 * scale * (S:ℝ)^2 * (1/(((modeCount D-S : ℕ):ℝ)-1)) := by
  let N := modeCount D-S
  have h2N : 2 ≤ N := (le_max_left _ _).trans hN
  have hSN : S ≤ N := (le_max_right _ _).trans hN
  have hcount : N+S = modeCount D := Nat.sub_add_cancel (by omega)
  have hN' : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 ≤ scale := by unfold scale; positivity
  let g (m : ℕ) := gaussianMode gaussianRate m
  let diff (m : ℕ) (t : ℝ) := g m t - g (m+S) t
  let second (m : ℕ) (t : ℝ) := diff m t - diff (m+S) t
  let F (j : ℕ) (t : ℝ) := kernel x t * (v w (N+j) * (diff (N+j) t : ℂ))
  let G (j : ℕ) (t : ℝ) := kernel x t * (v w (N+j) * (second (N+j) t : ℂ))
  have hg m := integrableOn_gaussianMode gaussianRate rate_pos m
  have hgr m := integrableOn_rootedGaussian gaussianRate rate_pos m
  have hdiff m : IntegrableOn (diff m) (Ioi 0) := (hg _).sub (hg _)
  have hdiffR m : IntegrableOn (fun t => diff m t / Real.sqrt t) (Ioi 0) := by
    simpa only [diff, sub_div, g, rootedGaussian] using (hgr m).sub (hgr (m+S))
  have hsecond m : IntegrableOn (second m) (Ioi 0) := (hdiff _).sub (hdiff _)
  have hsecondR m : IntegrableOn (fun t => second m t / Real.sqrt t) (Ioi 0) := by
    simpa only [second, sub_div] using (hdiffR m).sub (hdiffR (m+S))
  have hF j : IntegrableOn (F j) (Ioi 0) := kernel_mul_integrable x _ (hdiff _) (hdiffR _)
  have hG j : IntegrableOn (G j) (Ioi 0) := kernel_mul_integrable x _ (hsecond _) (hsecondR _)
  have hv m : ‖v w m‖ ≤ 1 := weightedPhase_bound w hw m
  have hE j : (∫ t in Ioi (0:ℝ), ‖F j t‖) ≤ scale*(5/2)*S*(1/((N:ℝ)-1)) := by
    calc
      _ ≤ ∫ t in Ioi (0:ℝ), ‖diff (N+j) t / Real.sqrt t‖ :=
        integral_norm_kernel_mul_le x (hv _) (hdiff _) (hdiffR _)
      _ ≤ scale*(5/2)*S/(N+j : ℕ) := by
        simpa only [scale, g, diff, sub_div, rootedGaussian] using
          integral_rootedGaussian_sub_le _ rate_pos (N+j) S (by omega) (by omega)
      _ ≤ _ := by
        have hb : (N:ℝ) - 1 ≤ ((N+j:ℕ):ℝ) := by
          have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
          push_cast
          linarith
        have h := div_le_div_of_nonneg_left (by positivity : 0 ≤ scale*(5/2)*S) (sub_pos.mpr hN') hb
        simpa only [div_eq_mul_inv, one_mul] using h
  have hP j : (∫ t in Ioi (0:ℝ), ‖G j t‖) ≤
      (scale*(51/4)*(S:ℝ)^2)*(1/(((N+j:ℕ):ℝ)^2)) := by
    have hre t : second (N+j) t = g (N+j) t - 2*g (N+j+S) t + g (N+j+2*S) t := by
      simp only [second, diff, show N+j+S+S=N+j+2*S by omega]
      ring
    calc
      _ ≤ ∫ t in Ioi (0:ℝ), ‖second (N+j) t / Real.sqrt t‖ :=
        integral_norm_kernel_mul_le x (hv _) (hsecond _) (hsecondR _)
      _ ≤ scale*(51/4)*((S:ℝ)/(N+j : ℕ))^2 := by
        simp_rw [hre, add_div, sub_div, mul_div_assoc]
        exact integral_rootedGaussian_second_sub_le _ rate_pos (N+j) S (by omega) (by omega)
      _ = _ := by ring
  have hs : Summable (fun j : ℕ => 1/(((N+j : ℕ):ℝ)^2)) := by
    simpa only [Nat.add_comm N] using (summable_nat_add_iff N).2
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  have hmajor := hs.mul_left (scale*(51/4)*(S:ℝ)^2)
  have hsum : Summable (fun j => ∫ t in Ioi (0:ℝ), ‖G j t‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hP hmajor
  let P (M : ℕ) (t : ℝ) :=
    kernel x t * recoveredThetaUpTo (observe D mockCoeff) w M (cuspRay t)
  let total (t : ℝ) := kernel x t * weightedCuspTheta w t
  have hpoint (t : ℝ) (ht : 0 < t) : total t - (P N t + P (N+S) t)/2 =
      ((∑ j ∈ Finset.range S, F j t) + ∑' j, G j t)/2 := by
    have hre j : second (N+j) t = g (N+j) t - 2*g (N+j+S) t + g (N+j+2*S) t := by
      simp only [second, diff, show N+j+S+S=N+j+2*S by omega]
      ring
    simp only [total, P, recoveredThetaUpTo_ray D N w t (Nat.sub_le ..),
      recoveredThetaUpTo_ray D (N+S) w t hcount.le,
      F, G, diff, hre, ← Finset.mul_sum, tsum_mul_left, g]
    have h := gaussian_average_tail S N w ha hw t ht
    dsimp only [v] at h ⊢
    linear_combination kernel x t * h / 2
  have h1 : IntegrableOn (P N) (Ioi 0) := polynomial_integrable D N w x (Nat.sub_le ..)
  have h2 : IntegrableOn (P (N+S)) (Ioi 0) := polynomial_integrable D _ w x hcount.le
  have hrec : IntegrableOn (fun t => (P N t+P (N+S) t)/2) (Ioi 0) :=
    (h1.add h2).div_const _
  have hedge : IntegrableOn (fun t => ∑ j ∈ Finset.range S, F j t) (Ioi 0) :=
    integrable_finset_sum _ (fun _ _ => hF _)
  have htail : IntegrableOn (fun t => ∑' j, G j t) (Ioi 0) :=
    integrable_tsum_of_summable_integral_norm G hG hsum
  have he : IntegrableOn (fun t => ((∑ j ∈ Finset.range S, F j t) + ∑' j, G j t)/2) (Ioi 0) :=
    (hedge.add htail).div_const _
  have herr := he.congr_fun (fun t ht => (hpoint t ht).symm) measurableSet_Ioi
  have htotal : IntegrableOn total (Ioi 0) :=
    (herr.add hrec).congr (Eventually.of_forall (fun _ => sub_add_cancel _ _))
  have hval : weightedCuspPeriod w x - averagedPeriod (observe D mockCoeff) w S x =
      ((∑ j ∈ Finset.range S, ∫ t in Ioi (0:ℝ), F j t) +
      ∑' j, ∫ t in Ioi (0:ℝ), G j t)/2 := by
    unfold averagedPeriod
    change (∫ t in Ioi (0:ℝ), total t) -
      ((∫ t in Ioi (0:ℝ), P N t) + (∫ t in Ioi (0:ℝ), P (modeCount D) t))/2 = _
    rw [← hcount, ← integral_add h1 h2, ← integral_div, ← integral_sub htotal hrec,
      setIntegral_congr_fun measurableSet_Ioi hpoint, integral_div, integral_add hedge htail,
      integral_finset_sum _ (fun _ _ => hF _), ← integral_tsum_of_summable_integral_norm hG hsum]
  have hfinite : ‖∑ j ∈ Finset.range S, ∫ t in Ioi (0:ℝ), F j t‖ ≤
      (S:ℝ)*(scale*(5/2)*S*(1/((N:ℝ)-1))) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _j ∈ Finset.range S, scale*(5/2)*S*(1/((N:ℝ)-1)) :=
        Finset.sum_le_sum (fun j _ => (norm_integral_le_integral_norm _).trans (hE j))
      _ = _ := by simp
  have hnorm : Summable (fun j => ‖∫ t in Ioi (0:ℝ), G j t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _) hsum
  have hinfinite : ‖∑' j, ∫ t in Ioi (0:ℝ), G j t‖ ≤
      (scale*(51/4)*(S:ℝ)^2)*(1/((N:ℝ)-1)) := by
    refine (norm_tsum_le_tsum_norm hnorm).trans ?_
    calc
      _ ≤ ∑' j : ℕ, (scale*(51/4)*(S:ℝ)^2)*(1/(((N+j:ℕ):ℝ)^2)) :=
        hnorm.tsum_le_tsum (fun j => (norm_integral_le_integral_norm _).trans (hP j)) hmajor
      _ ≤ _ := by
        rw [hs.tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (squareTail_le N h2N) (by positivity)
  refine ⟨htotal, ?_⟩
  rw [norm_sub_rev, hval, norm_div, show ‖(2:ℂ)‖ = 2 by norm_num]
  refine (div_le_div_of_nonneg_right ((norm_add_le _ _).trans (add_le_add hfinite hinfinite)) (by norm_num)).trans ?_
  change _ ≤ 8*scale*(S:ℝ)^2*(1/((N:ℝ)-1))
  calc
    _ = (61/8) * (scale*(S:ℝ)^2*(1/((N:ℝ)-1))) := by ring
    _ ≤ 8 * (scale*(S:ℝ)^2*(1/((N:ℝ)-1))) :=
      mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg (by positivity)
        (one_div_nonneg.mpr (sub_nonneg.mpr hN'.le)))
    _ = _ := by ring

theorem averagedPeriod_error (D : ℕ) (w : Phase → ℂ) (hw : ∀ r, ‖w r‖ ≤ 1)
    (hN : 1584 ≤ modeCount D-1584) (x : ℝ) :
    ‖averagedPeriod (observe D mockCoeff) w 1584 x - weightedCuspPeriod w x‖ ≤
      8*(Real.sqrt Real.pi / Real.sqrt gaussianRate)*(1584:ℝ)^2 *
        (1/(((modeCount D-1584 : ℕ):ℝ)-1)) :=
  (averagedPeriod_control_of_shift D 1584 w hw (weightedPhase_add_1584 w) (by omega) x).2

theorem averagedFullPeriod_error (D : ℕ) (hN : 144 ≤ modeCount D-144) (x : ℝ) :
    ‖averagedPeriod (observe D mockCoeff) (fun _ => 1) 144 x - fktyCuspPeriod x‖ ≤
      8*(Real.sqrt Real.pi / Real.sqrt gaussianRate)*(144:ℝ)^2 *
        (1/(((modeCount D-144 : ℕ):ℝ)-1)) := by
  rw [← weightedCuspPeriod_one]
  exact (averagedPeriod_control_of_shift D 144 (fun _ => 1) (fun _ => by simp)
    (by simpa only [v, one_mul] using fktyCuspPhase_add_144) (by omega) x).2

private theorem modeCount_sub_tendsto (S : ℕ) :
    Tendsto (fun D : ℕ => modeCount D-S) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [eventually_ge_atTop ((K+S)^2)] with D hD
  have hd : (K+S)^2 ≤ 24*D+1 := hD.trans (by omega)
  have h : K+S ≤ (24*D+1).sqrt := Nat.le_sqrt.mpr (by simpa only [pow_two] using hd)
  unfold modeCount
  omega

private theorem eventually_modeCount_sub_ge (S K : ℕ) :
    ∀ᶠ D : ℕ in atTop, K ≤ modeCount D-S :=
  tendsto_atTop.1 (modeCount_sub_tendsto S) K

theorem integrableOn_weightedCuspPeriod (w : Phase → ℂ) (hw : ∀ r, ‖w r‖ ≤ 1) (x : ℝ) :
    IntegrableOn (fun t => fktyVerticalKernel (-1/24) x t * weightedCuspTheta w t) (Ioi 0) := by
  obtain ⟨D, hD⟩ := (eventually_modeCount_sub_ge 1584 (max 2 1584)).exists
  exact (averagedPeriod_control_of_shift D 1584 w hw (weightedPhase_add_1584 w) hD x).1

private theorem averagedPeriod_uniform_of_shift (S : ℕ) (w : Phase → ℂ)
    (hw : ∀ r, ‖w r‖ ≤ 1) (ha : ∀ m, v w (m+S) = -v w m) :
    TendstoUniformlyOn (fun D x => averagedPeriod (observe D mockCoeff) w S x)
      (weightedCuspPeriod w) atTop Set.univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (modeCount_sub_tendsto (S+1))).const_mul (8*scale*(S:ℝ)^2)
  rw [mul_zero] at hlim
  filter_upwards [(tendsto_order.1 hlim).2 ε hε, eventually_modeCount_sub_ge S (max 2 S)] with D hD hN
  intro x _
  rw [dist_eq_norm, norm_sub_rev]
  have hc : ((modeCount D-(S+1) : ℕ) : ℝ) = ((modeCount D-S : ℕ) : ℝ)-1 := by
    rw [← Nat.sub_sub, Nat.cast_sub (show 1 ≤ modeCount D-S by omega), Nat.cast_one]
  exact (averagedPeriod_control_of_shift D S w hw ha hN x).2.trans_lt
    (by simpa only [Function.comp_apply, hc] using hD)

theorem averagedPeriod_uniform (w : Phase → ℂ) (hw : ∀ r, ‖w r‖ ≤ 1) :
    TendstoUniformlyOn (fun D x => averagedPeriod (observe D mockCoeff) w 1584 x)
      (weightedCuspPeriod w) atTop Set.univ :=
  averagedPeriod_uniform_of_shift 1584 w hw (weightedPhase_add_1584 w)

theorem averagedFullPeriod_uniform :
    TendstoUniformlyOn (fun D x => averagedPeriod (observe D mockCoeff) (fun _ => 1) 144 x)
      fktyCuspPeriod atTop Set.univ := by
  rw [← show weightedCuspPeriod (fun _ => 1) = fktyCuspPeriod by
    funext x
    exact weightedCuspPeriod_one x]
  exact averagedPeriod_uniform_of_shift 144 (fun _ => 1) (fun _ => by simp)
    (by simpa only [v, one_mul] using fktyCuspPhase_add_144)

private theorem kernel_at_cusp (t : ℝ) (ht : 0 < t) :
    kernel s t = I^(1/2 : ℂ) / (Real.sqrt t : ℂ) := by
  rw [kernel, fktyVerticalKernel, show (s : ℂ) + (t : ℂ)*I - (s : ℂ) = (t : ℂ)*I by ring,
    root_I_mul t ht]
  have hr : (I^(1/2:ℂ))^2 = I := by
    rw [← cpow_mul_nat]
    norm_num
  have hi := cpow_ne_zero_iff.mpr (Or.inl I_ne_zero : I ≠ 0 ∨ (1/2:ℂ) = 0)
  field_simp [hi, ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht).ne']
  exact hr.symm

private theorem scale_eq_fkty : (scale:ℂ) * I^(1/2 : ℂ) = fktyScale := by
  rw [fktyScale, ← Complex.ofReal_ofNat 12, root_I_mul _ (by norm_num)]
  congr 2
  unfold scale gaussianRate
  rw [Real.sqrt_div Real.pi_pos.le]
  field_simp [(Real.sqrt_pos.2 Real.pi_pos).ne']

private theorem integral_mode_cusp (w : Phase → ℂ) (m : ℕ) :
    (∫ t in Ioi (0:ℝ), kernel s t * (v w m * (gaussianMode gaussianRate m t : ℂ))) =
      fktyScale * v w m := by
  by_cases hm : m = 0
  · simp [hm, v, fktyCuspPhase, shadowSign, gaussianMode]
  calc
    _ = ∫ t in Ioi (0:ℝ), (I^(1/2:ℂ) * v w m) * (rootedGaussian gaussianRate m t : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change kernel s t * (v w m * (gaussianMode gaussianRate m t : ℂ)) =
        (I^(1/2:ℂ)*v w m) * (rootedGaussian gaussianRate m t : ℂ)
      rw [kernel_at_cusp t ht, rootedGaussian, ofReal_div]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_complex_ofReal,
        integral_rootedGaussian _ rate_pos m (Nat.pos_of_ne_zero hm), ← scale_eq_fkty]
      unfold scale
      push_cast
      ring

theorem periodUpTo_cusp (D N : ℕ) (w : Phase → ℂ) (hN : N ≤ modeCount D) :
    periodUpTo (observe D mockCoeff) w N (-1/24) =
      2*fktyScale*∑ m ∈ Finset.range N, (w (phase m) * fktyCuspPhase m) := by
  unfold periodUpTo
  have he (t : ℝ) : kernel (-1/24) t * recoveredThetaUpTo (observe D mockCoeff) w N (cuspRay t) =
      2*∑ m ∈ Finset.range N, kernel s t * (v w m * (gaussianMode gaussianRate m t : ℂ)) := by
    rw [recoveredThetaUpTo_ray D N w t hN]
    simp only [v, ← Finset.mul_sum]
    change kernel s t * (2 * _) = _
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_finset_sum _ (fun m _ => mode_integrable s w m)]
  simp_rw [integral_mode_cusp, ← Finset.mul_sum]
  unfold v
  ring

private theorem averagedPeriod_cusp_of_shift (D S : ℕ) (w : Phase → ℂ)
    (ha : ∀ m, v w (m+S) = -v w m) (hD : S ≤ modeCount D) :
    averagedPeriod (observe D mockCoeff) w S (-1/24) =
      fktyScale * ∑ m ∈ Finset.range S, v w m := by
  let N := modeCount D-S
  have hs : (∑ m ∈ Finset.range (modeCount D), v w m) =
      (∑ m ∈ Finset.range S, v w m) - ∑ m ∈ Finset.range N, v w m := by
    have he : S+N = modeCount D := by omega
    rw [← he, Finset.sum_range_add]
    simp only [Nat.add_comm S, ha, Finset.sum_neg_distrib, sub_eq_add_neg]
  unfold averagedPeriod
  rw [periodUpTo_cusp D N w (Nat.sub_le ..), periodUpTo_cusp D _ w le_rfl]
  change (2*fktyScale*(∑ m ∈ Finset.range N, v w m) +
    2*fktyScale*(∑ m ∈ Finset.range (modeCount D), v w m))/2 = _
  rw [hs]
  ring

/-- The sector-compatible average is exact at the diagonal cusp as soon as
one full sign-reversing shift is present. -/
theorem averagedPeriod_cusp (D : ℕ) (w : Phase → ℂ) (hD : 1584 ≤ modeCount D) :
    averagedPeriod (observe D mockCoeff) w 1584 (-1/24) =
      fktyScale * ∑ m ∈ Finset.range 1584, w (phase m) * fktyCuspPhase m :=
  averagedPeriod_cusp_of_shift D 1584 w (weightedPhase_add_1584 w) hD

theorem averagedFullPeriod_cusp (D : ℕ) (hD : 144 ≤ modeCount D) :
    averagedPeriod (observe D mockCoeff) (fun _ => 1) 144 (-1/24) =
      fktyScale * ∑ m ∈ Finset.range 144, fktyCuspPhase m := by
  simpa only [v, one_mul] using averagedPeriod_cusp_of_shift D 144 (fun _ => 1)
    (by simpa only [v, one_mul] using fktyCuspPhase_add_144) hD

theorem weightedCuspPeriod_cusp (w : Phase → ℂ) (hw : ∀ r, ‖w r‖ ≤ 1) :
    weightedCuspPeriod w (-1/24) =
      fktyScale * ∑ m ∈ Finset.range 1584, w (phase m) * fktyCuspPhase m := by
  apply tendsto_nhds_unique ((averagedPeriod_uniform w hw).tendsto_at (Set.mem_univ (-1/24)))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_modeCount_sub_ge 0 1584] with D hD
  exact (averagedPeriod_cusp D w (by omega)).symm

theorem fktyCuspPeriod_cusp :
    fktyCuspPeriod (-1/24) = fktyScale * ∑ m ∈ Finset.range 144, fktyCuspPhase m := by
  apply tendsto_nhds_unique (averagedFullPeriod_uniform.tendsto_at (Set.mem_univ (-1/24)))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_modeCount_sub_ge 0 144] with D hD
  exact (averagedFullPeriod_cusp D (by omega)).symm

private theorem cuspPhase_add_288_mul (m k : ℕ) :
    fktyCuspPhase (m+288*k) = fktyCuspPhase m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc,
      show m+288*k+288 = m+288*k+144+144 by omega,
      fktyCuspPhase_add_144, fktyCuspPhase_add_144, neg_neg, ih]

private theorem sum_cuspPhase_period (k : ℕ) :
    (∑ m ∈ Finset.range (288*k), fktyCuspPhase m) = 0 := by
  have h : (∑ m ∈ Finset.range 288, fktyCuspPhase m) = 0 := by
    rw [show 288=144+144 by decide, Finset.sum_range_add]
    simp only [Nat.add_comm 144, fktyCuspPhase_add_144, Finset.sum_neg_distrib, add_neg_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, zero_add]
    simpa only [Nat.add_comm (288*k), cuspPhase_add_288_mul] using h

private def cutoffBefore (k : ℕ) : ℕ := 3456*(k+1)^2
private def cutoffAfter (k : ℕ) : ℕ := cutoffBefore k+24*(k+1)

private theorem modeCount_before (k : ℕ) : modeCount (cutoffBefore k) = 288*(k+1)+1 := by
  unfold modeCount cutoffBefore
  rw [show 24*(3456*(k+1)^2)+1 = (288*(k+1))^2+1 by ring,
    Nat.sqrt_add_eq' _ (by omega)]

private theorem modeCount_after (k : ℕ) : modeCount (cutoffAfter k) = 288*(k+1)+2 := by
  unfold modeCount cutoffAfter cutoffBefore
  rw [show 24*(3456*(k+1)^2+24*(k+1))+1 = (288*(k+1)+1)^2 by ring, Nat.sqrt_eq']

private theorem cutoffBefore_tendsto : Tendsto cutoffBefore atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop n] with k hk
  have hs : k+1 ≤ (k+1)^2 := by simpa only [pow_two] using Nat.le_mul_self (k+1)
  unfold cutoffBefore
  omega

private theorem cutoffAfter_tendsto : Tendsto cutoffAfter atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [tendsto_atTop.1 cutoffBefore_tendsto n] with k hk
  exact hk.trans (Nat.le_add_right _ _)

private theorem raw_period_before (k : ℕ) :
    recoveredPeriod (observe (cutoffBefore k) mockCoeff) (fun _ => 1) (-1/24) = 0 := by
  rw [← periodUpTo_all, periodUpTo_cusp _ _ _ le_rfl, modeCount_before]
  have hz : fktyCuspPhase 0 = 0 := by simp [fktyCuspPhase, shadowSign]
  have hp : fktyCuspPhase (288*(k+1)) = 0 := by
    simpa only [zero_add, hz] using cuspPhase_add_288_mul 0 (k+1)
  simp only [one_mul, Finset.sum_range_succ, sum_cuspPhase_period, hp, add_zero, mul_zero]

private theorem raw_period_after (k : ℕ) :
    recoveredPeriod (observe (cutoffAfter k) mockCoeff) (fun _ => 1) (-1/24) =
      2*fktyScale*fktyCuspPhase 1 := by
  rw [← periodUpTo_all, periodUpTo_cusp _ _ _ le_rfl, modeCount_after]
  have hz : fktyCuspPhase 0 = 0 := by simp [fktyCuspPhase, shadowSign]
  have hp : fktyCuspPhase (288*(k+1)) = 0 := by
    simpa only [zero_add, hz] using cuspPhase_add_288_mul 0 (k+1)
  have hq : fktyCuspPhase (288*(k+1)+1) = fktyCuspPhase 1 := by
    simpa only [Nat.add_comm 1] using cuspPhase_add_288_mul 1 (k+1)
  simp only [one_mul, show 288*(k+1)+2=(288*(k+1)+1)+1 by omega,
    Finset.sum_range_succ, sum_cuspPhase_period, hp, hq, add_zero, zero_add]

/-- The unaveraged S6 period polynomials have two distinct constant
subsequences at the singular cusp. -/
theorem rawFullPeriod_cusp_no_limit (L : ℂ) :
    ¬ Tendsto (fun D => recoveredPeriod (observe D mockCoeff) (fun _ => 1) (-1/24))
      atTop (𝓝 L) := by
  intro h
  have hb : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 L) :=
    (h.comp cutoffBefore_tendsto).congr raw_period_before
  have ha : Tendsto (fun _ : ℕ => 2*fktyScale*fktyCuspPhase 1) atTop (𝓝 L) :=
    (h.comp cutoffAfter_tendsto).congr raw_period_after
  have h0 : L = 0 := tendsto_nhds_unique hb tendsto_const_nhds
  have h1 : L = 2*fktyScale*fktyCuspPhase 1 := tendsto_nhds_unique ha tendsto_const_nhds
  have hscale : fktyScale ≠ 0 := cpow_ne_zero_iff.mpr
    (Or.inl (mul_ne_zero (by norm_num : (12:ℂ) ≠ 0) I_ne_zero))
  have hphase : fktyCuspPhase 1 ≠ 0 := by
    simp [fktyCuspPhase, shadowSign, Complex.exp_ne_zero]
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hscale) hphase) (h1.symm.trans h0)

end MockThetaAnalytic.ShadowEndpoint
