import MockHolomorphic
import FORRadialProducts

/-! Fine's expansion for the third-order rank series. A shift of a convergent
series with a finite Pochhammer denominator gives a two-parameter recurrence.
Successive substitutions along the diagonal recover the defining square
exponents of Ramanujan's f. -/

noncomputable section
namespace MockThetaAnalytic
open Filter
open scoped Topology

private def fineDen (q : ℂ) (s m : ℕ) : ℂ :=
  ∏ j ∈ Finset.range m, (1+q^(s+j+1))

private def fineTerm (q : ℂ) (s : ℕ) (a : ℂ) (m : ℕ) : ℂ := a^m / fineDen q s m
private def fineSum (q : ℂ) (s : ℕ) (a : ℂ) : ℂ := ∑' m : ℕ, fineTerm q s a m

private theorem fineDen_succ (q : ℂ) (s m : ℕ) :
    fineDen q s (m+1) = fineDen q s m * (1+q^(s+m+1)) := by
  simp only [fineDen, Finset.prod_range_succ]

private theorem fineDen_head (q : ℂ) (s m : ℕ) :
    fineDen q s (m+1) = (1+q^(s+1)) * fineDen q (s+1) m := by
  rw [fineDen, Finset.prod_range_succ']
  simp only [Nat.add_zero, fineDen, ← Nat.add_assoc, Nat.add_right_comm s _ 1]
  ring

private theorem fineTerm_summable {q a : ℂ} {c : ℝ}
    (hc : 0 < c) (hd : ∀ s m, c ≤ ‖fineDen q s m‖) (ha : ‖a‖ < 1) (s : ℕ) :
    Summable (fineTerm q s a) := by
  apply ((summable_geometric_of_lt_one (norm_nonneg a) ha).div_const c).of_norm_bounded
  intro m
  rw [fineTerm, norm_div, norm_pow]
  exact div_le_div_of_nonneg_left (by positivity) hc (hd s m)

private theorem fineSum_sub_one {q a : ℂ} {s : ℕ} (hs : Summable (fineTerm q s a)) :
    fineSum q s a - 1 = ∑' m : ℕ, fineTerm q s a (m+1) := by
  have h := hs.sum_add_tsum_nat_add 1
  simp [fineTerm, fineDen] at h
  change (∑' m : ℕ, fineTerm q s a m) - 1 = _
  unfold fineTerm fineDen
  linear_combination -h

private theorem fineSum_shift {q a : ℂ} {s : ℕ} {c : ℝ} (hc : 0 < c)
    (hd : ∀ s m, c ≤ ‖fineDen q s m‖) (ha : ‖a‖ < 1) :
    fineSum q s a - 1 = a/(1+q^(s+1)) * fineSum q (s+1) a := by
  rw [fineSum_sub_one (fineTerm_summable hc hd ha s), fineSum, ← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [fineTerm, fineTerm, fineDen_head, pow_succ, div_eq_mul_inv, mul_inv_rev]
  simp only [div_eq_mul_inv]
  ring

/-- Subtract the zeroth term and shift the denominator by one factor. -/
private theorem fineSum_recurrence {q a : ℂ} {s : ℕ} {c : ℝ} (hc : 0 < c)
    (hd : ∀ s m, c ≤ ‖fineDen q s m‖) (hq : ‖q‖ < 1) (ha : ‖a‖ < 1) :
    (1-a) * fineSum q s a =
      1 - q^s * (a*q/(1+q^(s+1))) * fineSum q (s+1) (a*q) := by
  have haq : ‖a*q‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg a) hq.le).trans_lt ha
  have hsum := fineTerm_summable hc hd ha s
  have hsum' := fineTerm_summable hc hd haq s
  have hh : fineSum q s a - 1 + q^s*(fineSum q s (a*q) - 1) = a*fineSum q s a := by
    rw [fineSum_sub_one hsum, fineSum_sub_one hsum', ← tsum_mul_left,
      ← ((summable_nat_add_iff 1).2 hsum).tsum_add (((summable_nat_add_iff 1).2 hsum').mul_left _),
      fineSum, ← tsum_mul_left]
    apply tsum_congr
    intro m
    have nz : fineDen q s (m+1) ≠ 0 := norm_pos_iff.mp (hc.trans_le (hd _ _))
    have nd : fineDen q s m ≠ 0 := norm_pos_iff.mp (hc.trans_le (hd _ _))
    rw [fineDen_succ] at nz
    have nf := (mul_ne_zero_iff.mp nz).2
    simp only [fineTerm, fineDen_succ, mul_pow, pow_succ a m, show s+m+1=s+(m+1) by omega, pow_add q s (m+1)]
    rw [show s+m+1=s+(m+1) by omega, pow_add] at nf
    field_simp [nd, nf]
  rw [fineSum_shift hc hd haq] at hh
  linear_combination hh

private theorem norm_fineSum_le {q a : ℂ} (s : ℕ) {c : ℝ} (hc : 0 < c)
    (hd : ∀ s m, c ≤ ‖fineDen q s m‖) (hq : ‖q‖ < 1) (ha : ‖a‖ ≤ ‖q‖) :
    ‖fineSum q s a‖ ≤ (1-‖q‖)⁻¹ / c := by
  have hmajor := (summable_geometric_of_lt_one (norm_nonneg q) hq).div_const c
  have h : ∀ m : ℕ, ‖fineTerm q s a m‖ ≤ ‖q‖^m / c := by
    intro m
    rw [fineTerm, norm_div, norm_pow]
    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg a) ha _) hc (hd _ _)
  calc
    _ ≤ ∑' m : ℕ, ‖fineTerm q s a m‖ :=
      norm_tsum_le_tsum_norm ((fineTerm_summable hc hd (ha.trans_lt hq) s).norm)
    _ ≤ ∑' m : ℕ, ‖q‖^m/c :=
      Summable.tsum_le_tsum h (fineTerm_summable hc hd (ha.trans_lt hq) s).norm hmajor
    _ = _ := by rw [tsum_div_const, tsum_geometric_of_lt_one (norm_nonneg q) hq]

/-- Choosing a = −q^(n+1) in the recurrence leaves this remainder after
the first n+1 terms of the defining f-series. -/
private def fineRem (q : ℂ) (n : ℕ) : ℂ :=
  q^((n+1)*(n+1)) / (fineDen q 0 n * fineDen q 0 (n+1)) *
    fineSum q (n+1) (-q^(n+1))

/-- Consecutive remainders recover a single square-exponent term of f. -/
private theorem rem_step {q : ℂ} {c : ℝ} (hc : 0 < c)
    (hd : ∀ s m, c ≤ ‖fineDen q s m‖) (hq : ‖q‖ < 1) (n : ℕ) :
    fineRem q n = radialFTerm (n+1) q + fineRem q (n+1) := by
  have negnorm : ‖-q^(n+1)‖ < 1 := by
    rw [norm_neg, norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero n)
  have h := fineSum_recurrence (s := n+1) hc hd hq negnorm
  rw [neg_mul, ← pow_succ] at h
  have dn : fineDen q 0 n ≠ 0 := norm_pos_iff.mp (hc.trans_le (hd 0 n))
  have P (k : ℕ) : 1 + q^(k+1) ≠ 0 := by
    have h' : fineDen q 0 (k+1) ≠ 0 := norm_pos_iff.mp (hc.trans_le (hd _ _))
    simpa [fineDen_succ] using (show 1 + q^(0+k+1) ≠ 0 by
      rw [fineDen_succ] at h'
      exact (mul_ne_zero_iff.mp h').2)
  have hsq : (∏ j ∈ Finset.range (n+1), (1+q^(j+1))^2) = (fineDen q 0 (n+1))^2 := by
    simp [fineDen, Finset.prod_pow]
  rw [sub_neg_eq_add] at h
  unfold fineRem radialFTerm
  rw [hsq, show (n+1+1)*(n+1+1)=(n+1)*(n+1)+(n+1)+(n+1+1) by ring, pow_add, pow_add]
  simp only [fineDen_succ, Nat.zero_add]
  field_simp [P n, P (n+1), dn] at h ⊢
  linear_combination (norm := ring_nf) q^((n+1)*(n+1)) * h

private theorem rem_tendsto_zero {q : ℂ} {c : ℝ} (hc : 0 < c)
    (hd : ∀ s m, c ≤ ‖fineDen q s m‖) (hq : ‖q‖ < 1) :
    Tendsto (fineRem q) atTop (𝓝 0) := by
  let B : ℝ := (1-‖q‖)⁻¹/c
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).div_const (c*c)
  apply squeeze_zero_norm (a := fun n : ℕ => (‖q‖^n / (c*c)) * B) _ (by simpa using hlim.mul_const B)
  intro n
  have ha : ‖-q^(n+1)‖ ≤ ‖q‖ := by
    rw [norm_neg, norm_pow]
    exact pow_le_of_le_one (norm_nonneg q) hq.le (Nat.succ_ne_zero n)
  rw [fineRem, norm_mul, norm_div, norm_mul, norm_pow]
  refine mul_le_mul ?_ (norm_fineSum_le _ hc hd hq ha) (norm_nonneg _) (by positivity)
  refine div_le_div₀ (by positivity) (pow_le_pow_of_le_one (norm_nonneg q) hq.le ?_)
    (mul_pos hc hc) (mul_le_mul (hd 0 n) (hd 0 (n+1)) hc.le (norm_nonneg _))
  exact Nat.le_trans (Nat.le_succ n) (Nat.le_mul_self (n+1))

private theorem radialF_fine_of_bound {q : ℂ} {c : ℝ} (hc : 0 < c)
    (hd : ∀ s m, c ≤ ‖fineDen q s m‖) (hq : ‖q‖ < 1) :
    radialF q = 2 - fineSum q 0 (-q) := by
  have hpart (n : ℕ) :
      (∑ j ∈ Finset.range (n+1), radialFTerm j q) = 1 + fineRem q 0 - fineRem q n := by
    induction n with
    | zero => simp [radialFTerm]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, rem_step hc hd hq n]
      ring
  have h1 := ((hasSum_radialF q hq).tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h2 := (tendsto_const_nhds (x := (1:ℂ) + fineRem q 0)).sub (rem_tendsto_zero hc hd hq)
  have he : radialF q = 1 + fineRem q 0 := by
    apply tendsto_nhds_unique h1
    exact (by simpa using h2 : Tendsto (fun n : ℕ => 1+fineRem q 0 - fineRem q n) atTop _).congr
      (fun n => (hpart n).symm)
  have hs := fineSum_shift (s := 0) hc hd (show ‖-q‖ < 1 by simpa using hq)
  rw [he]
  simp only [fineRem, Nat.zero_add, pow_one, fineDen, Finset.prod_range_zero,
    Finset.prod_range_one, one_mul]
  simp only [Nat.zero_add, pow_one] at hs
  linear_combination hs

/-- Absolute convergence of the single-denominator expansion at an interior nome. -/
theorem summable_rankFine (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun m : ℕ => (-q)^m / (∏ j ∈ Finset.range m, (1+q^(j+1)))) := by
  obtain ⟨c, hc, hd⟩ := exists_radialPlus_shift_lower q hq
  apply (fineTerm_summable (q := q) hc hd (show ‖-q‖ < 1 by simpa using hq) 0).congr
  intro m
  simp [fineTerm, fineDen]

/-- Fine's identity for the actual hypergeometric rank series throughout the disk. -/
theorem radialF_eq_two_sub_fine (q : ℂ) (hq : ‖q‖ < 1) :
    radialF q = 2 - ∑' m : ℕ, (-q)^m / (∏ j ∈ Finset.range m, (1+q^(j+1))) := by
  obtain ⟨c, hc, hd⟩ := exists_radialPlus_shift_lower q hq
  simpa [fineSum, fineTerm, fineDen] using radialF_fine_of_bound hc hd hq

end MockThetaAnalytic
