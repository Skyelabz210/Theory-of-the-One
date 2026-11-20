import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! A decreasing convex cutoff extracts the first moment of a periodic
zero-mean coefficient sequence. On each period we compare the cutoff with
the line through its endpoints. The errors telescope over consecutive blocks. -/

noncomputable section

namespace MockThetaAnalytic
open Filter Set
open scoped Topology

private def drop (w : ℕ → ℝ) (n : ℕ) := w n - w (n+1)

private theorem drop_mesh_antitone (W : ℝ → ℝ) (hc : ConvexOn ℝ (Ici 0) W)
    {h : ℝ} (hh : 0 < h) : Antitone (drop (fun n : ℕ => W (n*h))) := by
  apply antitone_nat_of_succ_le
  intro n
  let x := (n : ℝ)*h
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hh.le
  have H := hc.slope_mono_adjacent (x := x) (y := x+h) (z := x+h+h)
    hx (show 0 ≤ x+h+h by linarith) (by linarith) (by linarith)
  rw [show x+h+h-(x+h) = h by ring, show x+h-x = h by ring,
    div_le_div_iff_of_pos_right hh] at H
  simpa only [drop, Nat.cast_add, Nat.cast_one, add_mul, one_mul, x] using
    (show W (x+h) - W (x+h+h) ≤ W x - W (x+h) by linarith)

private theorem segment_bounds (w : ℕ → ℝ) (hw : Antitone (drop w))
    (b r L : ℕ) (hr : r ≤ L) :
    r * drop w (b+L) ≤ w b-w (b+r) ∧ w b-w (b+r) ≤ r * drop w b := by
  have he : (∑ j ∈ Finset.range r, drop w (b+j)) = w b - w (b+r) := by
    simpa [drop, Nat.add_assoc] using Finset.sum_range_sub' (fun j => w (b+j)) r
  rw [← he]
  constructor
  · calc
      _ = ∑ _j ∈ Finset.range r, drop w (b+L) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j hj => hw (by have := Finset.mem_range.mp hj; omega)
  · calc
      _ ≤ ∑ _j ∈ Finset.range r, drop w b :=
        Finset.sum_le_sum fun j _ => hw (Nat.le_add_right b j)
      _ = _ := by simp

private theorem interpolation_error (w : ℕ → ℝ) (hw : Antitone (drop w))
    (b r L : ℕ) (hL : 0 < L) (hr : r ≤ L) :
    |w (b+r)-w b + (r : ℝ)/L * (w b-w (b+L))| ≤
      r * (drop w b - drop w (b+L)) := by
  have hl : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hleft := segment_bounds w hw b r L hr
  have hfull := segment_bounds w hw b L L le_rfl
  have scaled := mul_le_mul_of_nonneg_left hfull.1 (show 0 ≤ (r:ℝ)/L by positivity)
  have scaled' := mul_le_mul_of_nonneg_left hfull.2 (show 0 ≤ (r:ℝ)/L by positivity)
  rw [← mul_assoc, div_mul_cancel₀ _ hl.ne'] at scaled scaled'
  exact abs_le.mpr ⟨by linarith [hleft.2], by linarith [hleft.1]⟩

private def moment (L : ℕ) (a : ℕ → ℂ) : ℂ :=
  -(∑ r ∈ Finset.range L, (r : ℂ)*a r) / L

private def errorConstant (L : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ r ∈ Finset.range L, ‖a r‖ * r

private theorem block_bound (L : ℕ) (hL : 0 < L) (a : ℕ → ℂ)
    (hz : ∑ r ∈ Finset.range L, a r = 0) (w : ℕ → ℝ) (hw : Antitone (drop w))
    (b : ℕ) :
    ‖(∑ r ∈ Finset.range L, a r * (w (b+r) : ℂ)) -
      moment L a * ((w b-w (b+L) : ℝ) : ℂ)‖ ≤
      errorConstant L a * (drop w b - drop w (b+L)) := by
  let e (r : ℕ) := w (b+r)-w b + (r : ℝ)/L*(w b-w (b+L))
  have H : (∑ r ∈ Finset.range L, a r * (e r : ℂ)) =
      (∑ r ∈ Finset.range L, a r * (w (b+r) : ℂ)) -
      moment L a * ((w b-w (b+L) : ℝ) : ℂ) := by
    have he (r : ℕ) : a r * (e r : ℂ) = a r * (w (b+r) : ℂ) -
        a r * (w b : ℂ) + ((r : ℂ)*a r) * (((w b-w (b+L) : ℝ) : ℂ) / L) := by
      simp only [e, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_div, Complex.ofReal_natCast]
      ring
    simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hz, zero_mul, sub_zero, moment]
    ring
  rw [← H]
  calc
    _ ≤ ∑ r ∈ Finset.range L, ‖a r * (e r : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.range L, (‖a r‖ * r) * (drop w b - drop w (b+L)) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (interpolation_error w hw b r L hL
        (Finset.mem_range.mp hr).le) (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

private theorem period_shift (a : ℕ → ℂ) (L : ℕ) (hp : ∀ n, a (n+L) = a n)
    (N r : ℕ) : a (N*L+r) = a r := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.succ_mul, Nat.add_right_comm, hp, ih]

private theorem blocks_bound (L : ℕ) (hL : 0 < L) (a : ℕ → ℂ)
    (hp : ∀ n, a (n+L) = a n) (hz : ∑ r ∈ Finset.range L, a r = 0)
    (w : ℕ → ℝ) (hw : Antitone (drop w)) (N : ℕ) :
    ‖(∑ n ∈ Finset.range (N*L), a n * (w n : ℂ)) -
      moment L a * ((w 0-w (N*L) : ℝ) : ℂ)‖ ≤
      errorConstant L a * (drop w 0 - drop w (N*L)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have H := block_bound L hL a hz w hw (N*L)
    rw [Nat.succ_mul, Finset.sum_range_add]
    simp only [period_shift a L hp]
    calc
      _ = ‖((∑ n ∈ Finset.range (N*L), a n * (w n : ℂ)) -
              moment L a * ((w 0-w (N*L) : ℝ) : ℂ)) +
            ((∑ r ∈ Finset.range L, a r * (w (N*L+r) : ℂ)) -
              moment L a * ((w (N*L)-w (N*L+L) : ℝ) : ℂ))‖ := by
          congr 1
          push_cast
          ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add ih H)
      _ = _ := by ring

private theorem mesh_bound (L : ℕ) (hL : 0 < L) (a : ℕ → ℂ)
    (hp : ∀ n, a (n+L) = a n) (hz : ∑ r ∈ Finset.range L, a r = 0)
    (w : ℕ → ℝ) (hw : Antitone (drop w)) (ha : Antitone w) (hs : Summable w) :
    ‖(∑' n, a n * (w n : ℂ)) - moment L a * (w 0 : ℂ)‖ ≤
      errorConstant L a * (w 0-w 1) := by
  have hsum : Summable (fun n => a n * (w n : ℂ)) := by
    apply (hs.norm.mul_left (∑ r ∈ Finset.range L, ‖a r‖)).of_norm_bounded
    intro n
    rw [norm_mul, Complex.norm_real]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have he : a n = a (n%L) := by
      have H := period_shift a L hp (n/L) (n%L)
      rwa [Nat.mul_comm, Nat.add_comm, Nat.mod_add_div] at H
    rw [he]
    exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.mod_lt _ hL))
  have htop : Tendsto (fun N : ℕ => N*L) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hL) tendsto_id
  have hlim := (hsum.hasSum.tendsto_sum_nat.comp htop).sub
    (tendsto_const_nhds (x := moment L a) |>.mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_const_nhds (x := w 0) |>.sub (hs.tendsto_atTop_zero.comp htop))))
  simp only [sub_zero] at hlim
  apply le_of_tendsto' hlim.norm
  intro N
  apply (blocks_bound L hL a hp hz w hw N).trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  have h0 := ha (a := N*L) (b := N*L+1) (Nat.le_succ _)
  unfold drop
  simp only [zero_add]
  linarith

/-- With an integrable mesh at each positive scale, a decreasing convex cutoff
converges to the negative first moment per period as the scale tends to zero. -/
theorem tendsto_periodic_convex_smoothing (L : ℕ) (hL : 0 < L) (a : ℕ → ℂ)
    (hper : ∀ n, a (n+L) = a n) (hzero : ∑ n ∈ Finset.range L, a n = 0)
    (W : ℝ → ℝ) (hW0 : W 0 = 1) (hcont : ContinuousAt W 0)
    (hanti : AntitoneOn W (Ici 0)) (hconv : ConvexOn ℝ (Ici 0) W)
    (hsum : ∀ h : ℝ, 0 < h → Summable (fun n : ℕ => W (n*h))) :
    Tendsto (fun h : ℝ => ∑' n : ℕ, a n * (W (n*h) : ℂ)) (𝓝[>] 0)
      (𝓝 (-(∑ n ∈ Finset.range L, (n : ℂ) * a n) / L)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ => 0)
    (h := fun h => errorConstant L a * (1-W h)) tendsto_const_nhds
  · simpa [hW0] using ((tendsto_const_nhds (x := errorConstant L a)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hcont.tendsto)).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := hh
    have ha : Antitone (fun n : ℕ => W (n*h)) := by
      intro n m hnm
      exact hanti (by positivity : 0 ≤ (n:ℝ)*h) (by positivity : 0 ≤ (m:ℝ)*h)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hnm) hpos.le)
    simpa [moment, hW0] using mesh_bound L hL a hper hzero (fun n : ℕ => W (n*h))
      (drop_mesh_antitone W hconv hpos) ha (hsum h hpos)

end MockThetaAnalytic
