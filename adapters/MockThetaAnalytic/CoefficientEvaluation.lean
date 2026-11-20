import FifthOrderSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Ring.GrindInstances

/-! Evaluation of integer coefficient rows for mock theta series: monomial shifts,
positive binomial reciprocals, and absolutely convergent regrouping by degree. -/

noncomputable section

namespace MockThetaAnalytic.CoefficientEvaluation
open KElimination MockTheta FifthOrderSeries
def weighted {R : Type*} [CommRing R] (a : ℕ → ℤ) (q : R) (d : ℕ) : R := (a d : R)*q^d

private theorem shifted_start {R : Type*} [CommRing R] (a : ℕ → ℤ) (q : R) (j : ℕ) :
    ∑ d ∈ Finset.range j, weighted (shift j a) q d = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  simp [weighted, shift, if_neg (Nat.not_le_of_lt (Finset.mem_range.mp hd))]

private theorem weighted_shift_tail {R : Type*} [CommRing R] (a : ℕ → ℤ) (q : R) (d j : ℕ) :
    weighted (shift j a) q (d+j) = q^j * weighted a q d := by
  simp [weighted, shift, pow_add]
  ring

private theorem shifted_finite {R : Type*} [CommRing R] (a : ℕ → ℤ) (q : R) (j N : ℕ) :
    ∑ d ∈ Finset.range N, weighted (shift j a) q d =
      q^j * ∑ d ∈ Finset.range (N-j), weighted a q d := by
  by_cases h : j ≤ N
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Finset.sum_range_add, shifted_start, zero_add, Nat.add_sub_cancel_left, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Nat.add_comm j d, weighted_shift_tail]
  · rw [Nat.sub_eq_zero_of_le (by omega), Finset.range_zero, Finset.sum_empty, mul_zero]
    apply Finset.sum_eq_zero
    intro d hd
    have hd := Finset.mem_range.mp hd
    simp [weighted, shift, if_neg (show ¬j ≤ d by omega)]

theorem eval_shift {R : Type*} [NormedField R] (a : ℕ → ℤ) (q A : R) (j : ℕ)
    (h : HasSum (weighted a q) A) : HasSum (weighted (shift j a) q) (q^j*A) := by
  rw [← add_zero (q^j*A), ← shifted_start a q j, ← hasSum_nat_add_iff]
  simpa only [weighted_shift_tail] using h.mul_left (q^j)

abbrev divide (a : ℕ → ℤ) (j : ℕ) (hj : 0 < j) := divideBinomial j hj (-1) a

theorem divide_eq (a : ℕ → ℤ) (j : ℕ) (hj : 0 < j) (d : ℕ) :
    divide a j hj d = a d + shift j (divide a j hj) d := by
  have h := congrFun (mulBinomial_divideBinomial j hj (-1) a) d
  simp only [mulBinomial, neg_one_mul] at h
  dsimp only [divide]
  omega

theorem divide_nonneg (a : ℕ → ℤ) (j : ℕ) (hj : 0 < j) (ha : ∀ d, 0 ≤ a d) (d : ℕ) :
    0 ≤ divide a j hj d := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    rw [divide_eq, shift]
    split_ifs with hd
    · exact add_nonneg (ha d) (ih _ (by omega))
    · simpa using ha d

/-- The recurrence for formal division by 1−q^j bounds every finite
weighted partial sum by the input sum divided by 1−r^j. -/
theorem summable_divide (a : ℕ → ℤ) (j : ℕ) (hj : 0 < j) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ d, 0 ≤ a d) (hs : Summable (weighted a r)) : Summable (weighted (divide a j hj) r) := by
  let b := divide a j hj
  have hn (n : ℕ) : 0 ≤ weighted b r n := mul_nonneg (Int.cast_nonneg (divide_nonneg a j hj ha n))
    (pow_nonneg hr _)
  have hgap : 0 < 1-r^j := sub_pos.mpr (pow_lt_one₀ hr hr1 hj.ne')
  apply summable_of_sum_range_le hn (c := (∑' d, weighted a r d)/(1-r^j))
  intro N
  have eqn d : weighted b r d = weighted a r d + weighted (shift j b) r d := by
    change ((divide a j hj d : ℤ) : ℝ) * _ = _
    rw [divide_eq a j hj d]
    simp [weighted, add_mul, b]
  have hpart : ∑ d ∈ Finset.range N, weighted b r d =
      (∑ d ∈ Finset.range N, weighted a r d) + r^j * ∑ d ∈ Finset.range (N-j), weighted b r d := by
    calc
      _ = ∑ d ∈ Finset.range N, (weighted a r d + weighted (shift j b) r d) :=
        Finset.sum_congr rfl (fun d _ => eqn d)
      _ = _ := by rw [Finset.sum_add_distrib, shifted_finite]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le N j))
    (fun i _ _ => hn i)
  have haSum : (∑ i ∈ Finset.range N, weighted a r i) ≤ ∑' i, weighted a r i := hs.sum_le_tsum (Finset.range N) (fun i _ => mul_nonneg (Int.cast_nonneg (ha i)) (pow_nonneg hr _))
  apply (le_div_iff₀ hgap).mpr
  nlinarith [mul_le_mul_of_nonneg_left hle (pow_nonneg hr j)]

theorem eval_divide {R : Type*} [NormedField R] (a : ℕ → ℤ) (q A : R) (j : ℕ) (hj : 0 < j)
    (h0 : 1-q^j ≠ 0) (ha : HasSum (weighted a q) A)
    (hb : Summable (weighted (divide a j hj) q)) :
    HasSum (weighted (divide a j hj) q) (A/(1-q^j)) := by
  let b := divide a j hj
  have h := ha.add (eval_shift b q _ j hb.hasSum)
  have he : HasSum (weighted b q) (A + q^j * ∑' d, weighted b q d) := h.congr_fun (fun d => by
    change ((divide a j hj d : ℤ) : R)*_ = _
    rw [divide_eq a j hj d]
    simp [weighted, add_mul, b])
  have hv := hb.hasSum.unique he
  have hsum : (∑' d, weighted b q d) = A/(1-q^j) := (eq_div_iff h0).mpr (by
    change (∑' d, weighted b q d) = _ at hv
    linear_combination hv)
  exact hsum ▸ hb.hasSum

theorem eval_one {R : Type*} [NormedField R] (q : R) :
    HasSum (weighted (oneSeries : ℕ → ℤ) q) 1 := by
  have hs : HasSum (weighted (oneSeries : ℕ → ℤ) q) (∑ d ∈ ({0} : Finset ℕ), weighted (oneSeries : ℕ → ℤ) q d) := hasSum_sum_of_ne_finset_zero (f := weighted (oneSeries : ℕ → ℤ) q)
    (s := {0}) (fun n hn => by simp [weighted, oneSeries, show n ≠ 0 by simpa using hn])
  simpa [weighted, oneSeries] using hs

theorem weighted_norm (a : ℕ → ℤ) (q : ℂ) (ha : ∀ d, 0 ≤ a d) (d : ℕ) :
    ‖weighted a q d‖ = weighted a ‖q‖ d := by
  simp only [weighted, norm_mul, norm_pow, Complex.norm_intCast, abs_of_nonneg (Int.cast_nonneg (ha d))]

private theorem sumBelow_int (f : ℕ → ℤ) (N : ℕ) :
    ResidueSeries.sumBelow N f = ∑ i ∈ Finset.range N, f i := by
  induction N with
  | zero => simp [ResidueSeries.sumBelow]
  | succ n ih => simp [ResidueSeries.sumBelow, Finset.sum_range_succ, ih]

/-- Regroup an absolutely summable family of shifted integer coefficient rows by degree.
The formal coefficient is a finite sum because the nth shift is at least n. -/
theorem hasSum_shifted_family (e : ℕ → ℕ) (he : ∀ n, n ≤ e n) (rows : ℕ → ℕ → ℤ)
    (q : ℂ) (values : ℕ → ℂ)
    (hc : ∀ n, HasSum (weighted (shift (e n) (rows n)) q) (values n))
    (hall : Summable (fun p : ℕ × ℕ => weighted (shift (e p.1) (rows p.1)) q p.2)) :
    HasSum (weighted (shiftedCoeff e rows) q) (∑' n, values n) := by
  let a (n : ℕ) := shift (e n) (rows n)
  have hcol (d : ℕ) : HasSum (fun n => weighted (a n) q d) (weighted (shiftedCoeff e rows) q d) := by
    have hzero (n : ℕ) (hn : n ∉ Finset.range (d+1)) : weighted (a n) q d = 0 := by
      have hde : d < e n := lt_of_lt_of_le (by simpa using hn) (he n)
      simp [weighted, a, shift, if_neg (Nat.not_le_of_lt hde)]
    have h : HasSum (fun n => weighted (a n) q d) (∑ n ∈ Finset.range (d+1), weighted (a n) q d) :=
      hasSum_sum_of_ne_finset_zero hzero
    simpa only [weighted, shiftedCoeff, sumBelow_int, Int.cast_sum, Finset.sum_mul, a] using h
  have hv : ∑' p : ℕ×ℕ, weighted (a p.1) q p.2 = ∑' n, values n :=
    (hall.hasSum.prod_fiberwise hc).tsum_eq.symm
  have hs := hall.prod_symm.hasSum.prod_fiberwise hcol
  have hswap := (Equiv.prodComm ℕ ℕ).tsum_eq (fun p => weighted (a p.1) q p.2)
  exact (hswap.trans hv) ▸ hs

end MockThetaAnalytic.CoefficientEvaluation
