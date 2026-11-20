import FORRadialProducts
import FORGaussFinite
import Mathlib.Analysis.Normed.Group.Tannery

/-! Gauss's theta product in the open unit disk. The finite Gaussian
coefficients are uniformly bounded. Dominated convergence therefore gives
the infinite alternating-square sum for the modular correction. -/

noncomputable section
namespace MockThetaAnalytic

open Filter Complex
open scoped Topology

private theorem gaussEuler_limit {q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (gaussEuler q) atTop (𝓝 (radialEulerProduct q)) :=
  (hasProd_radialPochhammers hq).1.tendsto_prod_nat

private theorem gaussWeight_bound {q : ℂ} (hq : ‖q‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n k, ‖gaussWeight q n k‖ ≤ C := by
  have ht := gaussEuler_limit hq
  obtain ⟨A, hA⟩ := ht.norm.bddAbove_range
  obtain ⟨B, hB⟩ := (ht.inv₀ (radialPochhammers_ne_zero hq).1).norm.bddAbove_range
  have ha (n : ℕ) : ‖gaussEuler q n‖ ≤ |A| := (hA ⟨n,rfl⟩).trans (le_abs_self A)
  have hb (n : ℕ) : ‖(gaussEuler q n)⁻¹‖ ≤ |B| := (hB ⟨n,rfl⟩).trans (le_abs_self B)
  refine ⟨|A| * (|B| * |B|), by positivity, fun n k => ?_⟩
  rw [gaussWeight]
  split_ifs
  · rw [div_eq_mul_inv, mul_inv_rev, norm_mul, norm_mul]
    gcongr
    · apply ha
    · apply hb
    · apply hb
  · simp only [norm_zero]
    positivity

private theorem index_twice_limit : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
  tendsto_atTop_mono (fun n => show n ≤ 2*n by omega) tendsto_id

private theorem gaussWeight_limit {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    Tendsto (fun n => gaussWeight q n k) atTop (𝓝 (radialEulerProduct q)⁻¹) := by
  have ht := gaussEuler_limit hq
  have hne := (radialPochhammers_ne_zero hq).1
  have hadd : Tendsto (fun n : ℕ => n+k) atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ n+k by omega) tendsto_id
  have hl := (ht.comp index_twice_limit).div
    ((ht.comp hadd).mul (ht.comp (tendsto_sub_atTop_nat k))) (mul_ne_zero hne hne)
  rw [show radialEulerProduct q / (radialEulerProduct q * radialEulerProduct q) =
    (radialEulerProduct q)⁻¹ by field_simp] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  simp [gaussWeight, hn]

private theorem gauss_odd_split (q : ℂ) (n : ℕ) :
    gaussEuler q (2*n) = (∏ j ∈ Finset.range n, (1-q^(2*j+1))) * gaussEuler (q^2) n := by
  induction n with
  | zero => simp [gaussEuler]
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by omega]
    rw [gaussEuler, Finset.prod_range_succ, Finset.prod_range_succ, ← gaussEuler, ih,
      Finset.prod_range_succ]
    simp only [gaussEuler, Finset.prod_range_succ, ← pow_mul]
    rw [show 2*(n+1) = 2*n+1+1 by omega]
    ring

private theorem gauss_odd_limit {q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n, (1-q^(2*j+1))) atTop
      (𝓝 (radialEulerProduct q / radialEulerProduct (q^2))) := by
  have h2 : ‖q^2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by decide)
  apply (((gaussEuler_limit hq).comp index_twice_limit).div
    (gaussEuler_limit h2) (radialPochhammers_ne_zero h2).1).congr'
  filter_upwards with n
  change gaussEuler q (2*n) / gaussEuler (q^2) n = _
  rw [gauss_odd_split, mul_div_cancel_right₀ _ (gaussEuler_ne_zero h2 n)]

/-- Gauss's square theta specialization at a nome in the open disk. -/
theorem radialPlus_mul_radialB_eq_gauss (q : ℂ) (hq : ‖q‖ < 1) :
    radialPlusProduct q * radialB q =
      1 + 2 * ∑' k : ℕ, (-1 : ℂ)^(k+1)*q^((k+1)^2) := by
  by_cases hq0 : q = 0
  · subst q
    simp [radialPlusProduct, radialB]
  have h2 : ‖q^2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by decide)
  let a (k : ℕ) : ℂ := (-1)^(k+1) * q^((k+1)^2)
  have ha (k : ℕ) : ‖a k‖ ≤ ‖q‖^k := by
    simp only [a, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact pow_le_pow_of_le_one (norm_nonneg _) hq.le (by nlinarith [Nat.zero_le (k^2)])
  obtain ⟨C,hC,hbd⟩ := gaussWeight_bound h2
  have ht : Tendsto (fun n => ∑' k : ℕ, a k * gaussWeight (q^2) n (k+1)) atTop
      (𝓝 (∑' k : ℕ, a k * (radialEulerProduct (q^2))⁻¹)) := by
    refine tendsto_tsum_of_dominated_convergence
      ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right C)
      (fun k => (gaussWeight_limit h2 (k+1)).const_mul (a k)) ?_
    filter_upwards with n k
    rw [norm_mul]
    exact mul_le_mul (ha k) (hbd n (k+1)) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
  have hr := (gaussWeight_limit h2 0).add (ht.const_mul 2)
  have hl := (gauss_odd_limit hq).pow 2
  have he := tendsto_nhds_unique (hl.congr' (by
    filter_upwards with n
    rw [(tsum_eq_sum (s := Finset.range n) (f := fun k => a k * gaussWeight (q^2) n (k+1))
      (by intro k hk; simp only [Finset.mem_range] at hk; simp [gaussWeight, show ¬k+1 ≤ n by omega]))]
    exact gauss_finite q hq0 hq n)) hr
  rw [tsum_mul_right] at he
  change radialPlusProduct q * radialB q = 1+2*(∑' k, a k)
  have E := (radialPochhammers_ne_zero hq).1
  have P := (radialPochhammers_ne_zero hq).2
  rw [← radialEuler_mul_plus hq] at he
  rw [radialB_eq_pochhammers hq]
  field_simp at he ⊢
  linear_combination he

/-- Gauss's identity with the zero mode included in the one-sided square sum. -/
theorem radialPlus_mul_radialB_eq_thetaHalf (q : ℂ) (hq : ‖q‖ < 1) :
    radialPlusProduct q * radialB q =
      2 * (∑' k : ℕ, (-1 : ℂ)^k * q^(k*k)) - 1 := by
  have hs : Summable (fun k : ℕ => (-1 : ℂ)^k * q^(k*k)) := by
    apply (summable_geometric_of_lt_one (norm_nonneg _) hq).of_norm_bounded
    intro k
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact pow_le_pow_of_le_one (norm_nonneg _) hq.le (by nlinarith [Nat.zero_le ((k-1)*(k-1))])
  rw [radialPlus_mul_radialB_eq_gauss q hq, hs.tsum_eq_zero_add]
  simp only [pow_zero, Nat.zero_mul, one_mul, sq]
  ring

end MockThetaAnalytic
