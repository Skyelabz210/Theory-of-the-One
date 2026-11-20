import CoefficientEvaluation

/-! Absolute convergence and exact evaluation of the signed inverse-squared
Pochhammer rows defining the third-order mock theta function f. -/

noncomputable section

namespace MockThetaAnalytic

open KElimination MockTheta CoefficientEvaluation

private abbrev signedDivide (a : ℕ → ℤ) (j : ℕ) (hj : 0 < j) :=
  divideBinomial j hj 1 a

private theorem signedDivide_eq (a : ℕ → ℤ) (j : ℕ) (hj : 0 < j) (d : ℕ) :
    signedDivide a j hj d = a d - shift j (signedDivide a j hj) d := by
  have h := congrFun (mulBinomial_divideBinomial j hj 1 a) d
  simp only [mulBinomial, one_mul] at h
  dsimp only [signedDivide]
  omega

/-- Replacing 1+q^j by 1−q^j preserves a coefficientwise absolute majorant. -/
private theorem divide_dominates {a b : ℕ → ℤ} (h : ∀ d, |a d| ≤ b d) (j : ℕ) (hj : 0 < j)
    (d : ℕ) : |signedDivide a j hj d| ≤ divide b j hj d := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    rw [signedDivide_eq, divide_eq, shift, shift]
    split_ifs with hd
    · rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans (by simpa only [abs_neg] using add_le_add (h d) (ih (d-j) (by omega)))
    · simpa using h d

private theorem weighted_le {a b : ℕ → ℤ} (h : ∀ d, |a d| ≤ b d) (q : ℂ) (d : ℕ) :
    ‖weighted a q d‖ ≤ weighted b ‖q‖ d := by
  simp only [weighted, norm_mul, Complex.norm_intCast, norm_pow]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg q) d)
  exact_mod_cast h d

/-- A signed row with sum A and a nonnegative majorant with real-radius sum B. -/
private def RowEstimate (q : ℂ) (a : ℕ → ℤ) (A : ℂ) (B : ℝ) : Prop :=
  HasSum (weighted a q) A ∧ ∃ b : ℕ → ℤ, (∀ d, |a d| ≤ b d) ∧ HasSum (weighted b ‖q‖) B

private theorem estimate_divide {q : ℂ} (hq : ‖q‖ < 1) {a : ℕ → ℤ} {A : ℂ} {B : ℝ}
    (h : RowEstimate q a A B) (j : ℕ) (hj : 0 < j) :
    RowEstimate q (signedDivide a j hj) (A / (1+q^j)) (B / (1-‖q‖^j)) := by
  obtain ⟨ha, b, hdom, hb⟩ := h
  let s := signedDivide a j hj
  let t := divide b j hj
  have ht := summable_divide b j hj (norm_nonneg q) hq (fun d => (abs_nonneg _).trans (hdom d))
    hb.summable
  have hst (d : ℕ) : |s d| ≤ t d := divide_dominates hdom j hj d
  have hs : Summable (weighted s q) := ht.of_norm_bounded (weighted_le hst q)
  have hp := pow_lt_one₀ (norm_nonneg q) hq hj.ne'
  have hz : 1+q^j ≠ 0 := by
    intro hzero
    have he : q^j = -1 := by linear_combination hzero
    have hn := congrArg norm he
    rw [norm_pow, norm_neg, norm_one] at hn
    exact hp.ne hn
  refine ⟨?_, t, hst, eval_divide _ _ _ j hj (sub_ne_zero.mpr hp.ne') hb ht⟩
  have hSum := ha.sub (eval_shift s q _ j hs.hasSum)
  have he : HasSum (weighted s q) (A - q^j * ∑' d, weighted s q d) := hSum.congr_fun (fun d => by
    change ((signedDivide a j hj d : ℤ) : ℂ) * _ = _
    rw [signedDivide_eq a j hj d]
    simp [weighted, sub_mul, s])
  have hv := hs.hasSum.unique he
  have hval : (∑' d, weighted s q d) = A / (1+q^j) := (eq_div_iff hz).mpr (by
    change (∑' d, weighted s q d) = _ at hv
    linear_combination hv)
  exact hval ▸ hs.hasSum

private theorem rowEstimate (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    RowEstimate q (inverseSquaredPochhammer n)
      ((∏ j ∈ Finset.range n, (1+q^(j+1))^2)⁻¹)
      ((∏ j ∈ Finset.range n, (1-‖q‖^(j+1))^2)⁻¹) := by
  induction n with
  | zero =>
    simp only [inverseSquaredPochhammer, Finset.range_zero, Finset.prod_empty, inv_one]
    exact ⟨eval_one _, oneSeries, fun d => by simp [oneSeries]; split <;> decide, eval_one _⟩
  | succ n ih =>
    have h := estimate_divide hq (estimate_divide hq ih (n+1) (by omega)) (n+1) (by omega)
    simpa only [inverseSquaredPochhammer, Finset.prod_range_succ, div_eq_mul_inv, mul_inv,
      pow_two, mul_assoc] using h

/-- Evaluation of the actual integer coefficients of the nth reciprocal row. -/
theorem thirdOrderRow (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    HasSum (weighted (inverseSquaredPochhammer n) q) ((∏ j ∈ Finset.range n, (1+q^(j+1))^2)⁻¹) :=
  (rowEstimate q hq n).1

/-- Absolute summability with a closed bound from the positive real-radius denominator. -/
theorem thirdOrderRowNorm (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    Summable (fun d => ‖weighted (inverseSquaredPochhammer n) q d‖) ∧
    (∑' d, ‖weighted (inverseSquaredPochhammer n) q d‖) ≤
      (∏ j ∈ Finset.range n, (1-‖q‖^(j+1))^2)⁻¹ := by
  obtain ⟨b, h, hb⟩ := (rowEstimate q hq n).2
  have hsum := Summable.of_nonneg_of_le (fun d => norm_nonneg _) (weighted_le h q) hb.summable
  exact ⟨hsum, hb.tsum_eq ▸ hsum.tsum_le_tsum (weighted_le h q) hb.summable⟩

end MockThetaAnalytic
