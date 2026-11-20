import CoefficientEvaluation
import MockThetaFifthZero
import MockThetaSeventh
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Algebra.Ring.GrindInstances

/-! Ramanujan's fifth-order χ₀ and seventh-order ℱ₀ share the denominator
(q^(n+1);q)_n. Their numerators are q^n and q^(n²), respectively. The absolute double
series lets us regroup the defining summands by degree and recover each
existing integer coefficient function on the whole unit disk. -/

noncomputable section

namespace MockThetaAnalytic

open KElimination Filter
open scoped Topology

/-- The common formal denominator inverse is the same coefficient constructor in both families. -/
theorem fifthChi0_seventhF0_factors (n d : ℕ) :
    (MockThetaFifthZero.factors .chi n d : ℤ) = MockThetaSeventh.factors .f0 n d := rfl

/-- The finite shared denominator (q^(n+1);q)_n. -/
def chi0Denominator (n : ℕ) (q : ℂ) : ℂ :=
  ∏ j ∈ Finset.range n, (1-q^(n+1+j))

private def term (e : ℕ → ℕ) (n : ℕ) (q : ℂ) : ℂ := q^(e n) / chi0Denominator n q

/-- Fifth-order χ₀ with numerator q^n. -/
def fifthChi0 (q : ℂ) : ℂ := ∑' n, term (MockThetaFifthZero.exponent .chi) n q

/-- Seventh-order ℱ₀ with numerator q^(n²). -/
def seventhF0 (q : ℂ) : ℂ := ∑' n, term (MockThetaSeventh.exponent .f0) n q

private def rowBound (r : ℝ) (n : ℕ) : ℝ := (r / (1-r^(n+1)))^n

/-- Eventually r^(n+1) < 1−c for some r<c<1, so the bound is at most (r/c)^n. -/
private theorem summable_rowBound {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) : Summable (rowBound r) := by
  obtain ⟨c, hrc, hc1⟩ := exists_between hr1
  have hc : 0 < c := hr.trans_lt hrc
  have hratio : ‖r/c‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr hc.le), div_lt_one hc]
    exact hrc
  apply (summable_geometric_of_norm_lt_one hratio).of_norm_bounded_eventually_nat
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
  filter_upwards [ht.eventually_lt_const (sub_pos.mpr hc1)] with n hn
  have hp : r^(n+1) ≤ r^n := pow_le_pow_of_le_one hr hr1.le (by omega)
  have hd : c ≤ 1-r^(n+1) := by linarith
  rw [rowBound, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (div_nonneg hr (hc.le.trans hd)) _)]
  exact pow_le_pow_left₀ (div_nonneg hr (hc.le.trans hd)) (div_le_div_of_nonneg_left hr hc hd) n

private theorem norm_factor_lower {q : ℂ} {r : ℝ} (hr : ‖q‖ ≤ r) (hr1 : r < 1) (n j : ℕ) :
    1-r^(n+1) ≤ ‖1-q^(n+1+j)‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (q^(n+1+j))
  rw [norm_one, norm_pow] at h
  have h0 := (norm_nonneg q).trans hr
  exact (sub_le_sub_left ((pow_le_pow_left₀ (norm_nonneg _) hr _).trans
    (pow_le_pow_of_le_one h0 hr1.le (by omega))) 1).trans h

private theorem factor_gap_pos {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    0 < 1-r^(n+1) := sub_pos.mpr (pow_lt_one₀ h0 h1 (Nat.succ_ne_zero _))

private theorem norm_term_le (e : ℕ → ℕ) (he : ∀ n, n ≤ e n) {q : ℂ} {r : ℝ}
    (hr : ‖q‖ ≤ r) (hr1 : r < 1) (n : ℕ) : ‖term e n q‖ ≤ rowBound r n := by
  have h0 := (norm_nonneg q).trans hr
  have hgap := factor_gap_pos h0 hr1 n
  have hden : (1-r^(n+1))^n ≤ ∏ j ∈ Finset.range n, ‖1-q^(n+1+j)‖ := by
    calc
      _ = ∏ _j ∈ Finset.range n, (1-r^(n+1)) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hgap.le) (fun j _ => norm_factor_lower hr hr1 n j)
  rw [term, rowBound, chi0Denominator, norm_div, norm_pow, norm_prod, div_pow]
  exact div_le_div₀ (pow_nonneg h0 n) ((pow_le_pow_left₀ (norm_nonneg _) hr _).trans
    (pow_le_pow_of_le_one h0 hr1.le (he n))) (pow_pos hgap _) hden

private theorem differentiableAt_term (e : ℕ → ℕ) (n : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (term e n) q := by
  unfold term chi0Denominator
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact norm_ne_zero_iff.mp ((factor_gap_pos (norm_nonneg q) hq n).trans_le
      (norm_factor_lower (le_refl _) hq n j)).ne'

private theorem differentiableAt_series (e : ℕ → ℕ) (he : ∀ n, n ≤ e n) (q : ℂ) (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (fun w => ∑' n, term e n w) q := by
  obtain ⟨r, hqr, hr⟩ := exists_between hq
  have hopen : IsOpen {w : ℂ | ‖w‖ < r} := isOpen_lt continuous_norm continuous_const
  have h := Complex.differentiableOn_tsum_of_summable_norm
    (summable_rowBound ((norm_nonneg q).trans hqr.le) hr)
    (fun n w hw => (differentiableAt_term e n w (lt_trans hw hr)).differentiableWithinAt)
    hopen (fun n w hw => norm_term_le e he (le_of_lt hw) hr n)
  exact h.differentiableAt (hopen.mem_nhds hqr)

theorem hasSum_fifthChi0 (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => q^n / chi0Denominator n q) (fifthChi0 q) :=
  ((summable_rowBound (norm_nonneg q) hq).of_norm_bounded
    (fun n => norm_term_le _ (MockThetaFifthZero.le_exponent .chi) (le_refl _) hq n)).hasSum

theorem hasSum_seventhF0 (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => q^(n*n) / chi0Denominator n q) (seventhF0 q) :=
  ((summable_rowBound (norm_nonneg q) hq).of_norm_bounded
    (fun n => norm_term_le _ (MockThetaSeventh.le_exponent .f0) (le_refl _) hq n)).hasSum

theorem differentiableAt_fifthChi0 (q : ℂ) (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ fifthChi0 q := differentiableAt_series _ (MockThetaFifthZero.le_exponent .chi) q hq

theorem differentiableAt_seventhF0 (q : ℂ) (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ seventhF0 q := differentiableAt_series _ (MockThetaSeventh.le_exponent .f0) q hq

open MockTheta FifthOrderSeries

open CoefficientEvaluation

private def row (n k : ℕ) : ℕ → ℤ := reciprocalProduct (n+1) 1 k (by omega) (-1)

private def partialDen {R : Type*} [CommRing R] (q : R) (n k : ℕ) : R :=
  ∏ j ∈ Finset.range k, (1-q^(n+1+j))

private theorem eval_row (q : ℂ) (hq : ‖q‖ < 1) (n k : ℕ) :
    (∀ d, 0 ≤ row n k d) ∧
    HasSum (weighted (row n k) ‖q‖) (partialDen ‖q‖ n k)⁻¹ ∧
    HasSum (weighted (row n k) q) (partialDen q n k)⁻¹ := by
  induction k with
  | zero =>
    simp only [row, reciprocalProduct, partialDen, Finset.range_zero, Finset.prod_empty, inv_one]
    exact ⟨fun d => by simp [oneSeries]; split <;> decide, eval_one _, eval_one _⟩
  | succ k ih =>
    obtain ⟨hn, hr, hc⟩ := ih
    let j := n+1+k
    have hj : 0 < j := by dsimp [j]; omega
    have he : row n (k+1) = divide (row n k) j hj := by
      unfold row divide j
      rw [reciprocalProduct]
      congr 1
      omega
    have hnew := divide_nonneg (row n k) j hj hn
    have hsr := summable_divide (row n k) j hj (norm_nonneg _) hq hn hr.summable
    have hsc := hsr.of_norm_bounded (fun d => (weighted_norm _ q hnew d).le)
    have hzr := (sub_pos.mpr (pow_lt_one₀ (norm_nonneg q) hq hj.ne')).ne'
    have hzc : 1-q^j ≠ 0 := norm_ne_zero_iff.mp
      ((factor_gap_pos (norm_nonneg q) hq n).trans_le (norm_factor_lower (le_refl _) hq n k)).ne'
    rw [he]
    refine ⟨hnew, ?_, ?_⟩
    · simpa only [partialDen, Finset.prod_range_succ, div_eq_mul_inv, mul_inv, j] using
        eval_divide _ _ _ j hj hzr hr hsr
    · simpa only [partialDen, Finset.prod_range_succ, div_eq_mul_inv, mul_inv, j] using
        eval_divide _ _ _ j hj hzc hc hsc

/-- Sum by the hypergeometric index and by coefficient degree. Positivity
at the real radius proves absolute summability of the joint series. -/
private theorem eval_family_coefficients (e : ℕ → ℕ) (he : ∀ n, n ≤ e n) (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (weighted (shiftedCoeff e (fun n => row n n)) q) (∑' n, term e n q) := by
  let a (n : ℕ) := shift (e n) (row n n)
  have hrow n := eval_row q hq n n
  have hpos (n d : ℕ) : 0 ≤ a n d := by
    simp only [a, shift]
    split_ifs with hd
    · exact (hrow n).1 _
    · exact le_refl _
  have hr n := eval_shift (row n n) ‖q‖ _ (e n) (hrow n).2.1
  have hc (n : ℕ) : HasSum (weighted (a n) q) (term e n q) := by
    simpa only [a, term, div_eq_mul_inv, chi0Denominator, partialDen] using
      eval_shift (row n n) q _ (e n) (hrow n).2.2
  have hsum : Summable (fun n => ‖q‖^(e n) * (partialDen ‖q‖ n n)⁻¹) := by
    apply (summable_rowBound (norm_nonneg q) hq).of_norm_bounded
    intro n
    have hcast : ((partialDen ‖q‖ n n : ℝ) : ℂ) = chi0Denominator n (‖q‖ : ℂ) := by
      simp [partialDen, chi0Denominator]
    rw [← Complex.norm_real, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv, hcast, ← div_eq_mul_inv]
    exact norm_term_le e he (by simp) hq n
  have hdbl : Summable (fun p : ℕ × ℕ => weighted (a p.1) ‖q‖ p.2) := by
    apply (summable_prod_of_nonneg (fun p => mul_nonneg (Int.cast_nonneg (hpos p.1 p.2)) (pow_nonneg (norm_nonneg _) _))).2
    refine ⟨fun n => (hr n).summable, ?_⟩
    exact hsum.congr (fun n => (hr n).tsum_eq.symm)
  have hall : Summable (fun p : ℕ × ℕ => weighted (a p.1) q p.2) :=
    hdbl.of_norm_bounded (fun p => (weighted_norm (a p.1) q (hpos p.1) p.2).le)
  exact hasSum_shifted_family e he (fun n => row n n) q (fun n => term e n q) hc hall

/-- Inside the unit disk the integer coefficient constructor sums to the defining χ₀ series. -/
theorem hasSum_fifthChi0_coefficients (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun d : ℕ => ((MockThetaFifthZero.chiCoeff d : ℤ) : ℂ) * q^d) (fifthChi0 q) :=
  eval_family_coefficients _ (MockThetaFifthZero.le_exponent .chi) q hq

/-- The independently defined seventh-order ℱ₀ coefficient constructor has this same
analytic interpretation, with square leading shifts. -/
theorem hasSum_seventhF0_coefficients (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun d : ℕ => ((MockThetaSeventh.f0Coeff d : ℤ) : ℂ) * q^d) (seventhF0 q) :=
  eval_family_coefficients _ (MockThetaSeventh.le_exponent .f0) q hq

end MockThetaAnalytic
