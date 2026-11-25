import FORCyclotomicBlock
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! At a primitive root of order 2k, the Watson series with the selected
denominator parity converges to twice its initial block, with the zero-index
term removed for ψ. The same endpoint terms dominate the radial series. -/

noncomputable section
namespace MockThetaAnalytic

open Complex Finset Filter Set
open scoped Topology

def watsonTerm (c : ℕ) (q : ℂ) (n : ℕ) : ℂ :=
  (-q)^(n^2) / ∏ j ∈ range n, (1+q^(2*j+c))

theorem watsonTerm_succ (c : ℕ) (q : ℂ) (n : ℕ) :
    watsonTerm c q (n+1) = watsonTerm c q n * ((-q)^(2*n+1)/(1+q^(2*n+c))) := by
  rw [watsonTerm, watsonTerm, prod_range_succ, show (n+1)^2=n^2+(2*n+1) by ring,
    pow_add, div_mul_div_comm]

theorem radialFactor_le (x : ℝ) (v : ℂ) (hv : ‖v‖ = 1) :
    x * ‖1+v‖ ≤ ‖1+(x:ℂ)^2*v‖ := by
  have hnorm : normSq v = 1 := by rw [normSq_eq_norm_sq, hv]; norm_num
  have h1 : ‖1+v‖^2 = 2+2*v.re := by
    simp [Complex.sq_norm, normSq_add, hnorm]; ring
  have h2 : ‖1+(x:ℂ)^2*v‖^2 = 1+x^4+2*x^2*v.re := by
    simp [Complex.sq_norm, normSq_add, normSq_mul, normSq_ofReal, hnorm,
      ← Complex.ofReal_pow, mul_assoc]; ring
  have h3 : (x * ‖1+v‖)^2 ≤ ‖1+(x:ℂ)^2*v‖^2 := by
    rw [mul_pow, h1, h2]; nlinarith [sq_nonneg (x^2-1)]
  exact le_of_sq_le_sq h3 (norm_nonneg _)

theorem watson_factor_ne_zero_of_half_power {q : ℂ} {k c : ℕ}
    (hq : q^k = -1) (hc : Odd (k+c)) (n : ℕ) : 1+q^(2*n+c) ≠ 0 := by
  intro h
  have hz : (-q^(2*n+c))^k = 1 := by
    rw [show q^(2*n+c) = -1 by linear_combination h, neg_neg, one_pow]
  rw [neg_pow, pow_right_comm q, hq, ← pow_add,
    show k+(2*n+c)=2*n+(k+c) by omega, pow_add, pow_mul, hc.neg_one_pow] at hz
  norm_num at hz

theorem watson_factor_ne_zero {ζ : ℂ} {k : ℕ} (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2*k))
    {c : ℕ} (hc : Odd (k+c)) (n : ℕ) : 1+ζ^(2*n+c) ≠ 0 :=
  watson_factor_ne_zero_of_half_power (primitive_even_half_power hk hζ) hc n

/-- On every ray, the selected Watson term is no larger than its own endpoint value. -/
theorem norm_watsonTerm_radial_le {ζ : ℂ} {k : ℕ} (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2*k))
    {c : ℕ} (hc : Odd (k+c)) (hc' : c ≤ 2) (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1) (n : ℕ) :
    ‖watsonTerm c ((t:ℂ)*ζ) n‖ ≤ ‖watsonTerm c ζ n‖ := by
  have hz := hζ.norm'_eq_one (by omega)
  induction n with
  | zero => simp [watsonTerm]
  | succ n ih =>
    rw [watsonTerm_succ, watsonTerm_succ, norm_mul, norm_mul]
    apply mul_le_mul ih _ (norm_nonneg _) (norm_nonneg _)
    let a := t^(2*n+c)
    let v := ζ^(2*n+c)
    have ha : 0 < a := pow_pos ht _
    have hv : ‖v‖ = 1 := by simp [v, hz]
    have hp : 0 < ‖1+v‖ := norm_pos_iff.mpr (watson_factor_ne_zero hk hζ hc n)
    have hs := radialFactor_le (Real.sqrt a) v hv
    rw [show ((Real.sqrt a : ℝ):ℂ)^2 = (a:ℂ) by rw [← ofReal_pow, Real.sq_sqrt ha.le]] at hs
    have hle : t^(2*n+1) ≤ Real.sqrt a := Real.le_sqrt_of_sq_le (by
      change (t^(2*n+1))^2 ≤ t^(2*n+c)
      rw [← pow_mul]
      exact pow_le_pow_of_le_one ht.le ht' (by omega))
    have hbound := (mul_le_mul_of_nonneg_right hle hp.le).trans hs
    have hx := (mul_pos (pow_pos ht (2*n+1)) hp).trans_le hbound
    have hd : t^(2*n+1) / ‖1+(a:ℂ)*v‖ ≤ 1 / ‖1+v‖ :=
      (div_le_div_iff₀ hx hp).mpr (by simpa using hbound)
    simpa only [a, v, norm_div, norm_neg, norm_pow, mul_pow, ofReal_pow, norm_mul,
      norm_real, Real.norm_eq_abs, abs_of_pos ht, hz, mul_one, one_pow] using hd

theorem watson_numerator_add_halfOrder {ζ : ℂ} {k : ℕ} (hk : 0 < k)
    (hζ : IsPrimitiveRoot ζ (2*k)) (n : ℕ) : (-ζ)^((n+k)^2) = (-ζ)^(n^2) := by
  have h2k : (-ζ)^(2*k) = 1 := by rw [(even_two.mul_right k).neg_pow, hζ.pow_eq_one]
  have hk2 : (-ζ)^(k*k) = 1 := by
    rw [pow_mul]
    rcases Nat.even_or_odd k with h | h
    · rw [h.neg_pow, primitive_even_half_power hk hζ, h.neg_one_pow]
    · rw [h.neg_pow, primitive_even_half_power hk hζ, neg_neg, one_pow]
  rw [show (n+k)^2=n^2+2*k*n+k*k by ring, pow_add, pow_add, pow_mul (-ζ) (2*k),
    h2k, hk2, one_pow, mul_one, mul_one]

theorem watsonTerm_add_halfOrder {ζ : ℂ} {k : ℕ} (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2*k))
    {c : ℕ} (hc : Odd (k+c)) (n : ℕ) : watsonTerm c ζ (n+k) = watsonTerm c ζ n / 2 := by
  rw [watsonTerm, watsonTerm, prod_range_add, watson_denominator_block hk hζ c hc n,
    watson_numerator_add_halfOrder hk hζ n, div_div]

theorem watsonTerm_geometric {ζ : ℂ} {k : ℕ} (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2*k))
    {c : ℕ} (hc : Odd (k+c)) (m r : ℕ) :
    watsonTerm c ζ (m*k+r) = (1/2:ℂ)^m * watsonTerm c ζ r := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show (m+1)*k+r=m*k+r+k by ring, watsonTerm_add_halfOrder hk hζ hc, ih, pow_succ]
    ring

theorem summable_norm_watsonTerm {ζ : ℂ} {k : ℕ} (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2*k))
    {c : ℕ} (hc : Odd (k+c)) : Summable (fun n : ℕ => ‖watsonTerm c ζ n‖) := by
  letI : NeZero k := ⟨hk.ne'⟩
  apply (Nat.divModEquiv k).symm.summable_iff.mp
  have hg : Summable (fun m : ℕ => (1/2:ℝ)^m) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hf := (hasSum_fintype (fun r : Fin k => ‖watsonTerm c ζ r.val‖)).summable
  apply (hg.mul_of_nonneg hf (fun m => by positivity) (fun _ => norm_nonneg _)).congr
  intro p
  simp [Nat.divModEquiv_symm_apply, watsonTerm_geometric hk hζ hc]

theorem watsonTerm_tsum_eq_two_mul_sum {ζ : ℂ} {k : ℕ} (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2*k))
    {c : ℕ} (hc : Odd (k+c)) :
    ∑' n : ℕ, watsonTerm c ζ n = 2 * ∑ n ∈ range k, watsonTerm c ζ n := by
  have h := (summable_norm_watsonTerm hk hζ hc).of_norm.sum_add_tsum_nat_add k
  simp_rw [watsonTerm_add_halfOrder hk hζ hc, div_eq_mul_inv] at h
  rw [tsum_mul_right] at h
  linear_combination -2*h

theorem watsonTerm_radial_limit {ζ : ℂ} {k : ℕ} (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2*k))
    {c : ℕ} (hc : Odd (k+c)) (hc' : c ≤ 2) (shift : ℕ) :
    Tendsto (fun t : ℝ => ∑' n : ℕ, watsonTerm c ((t:ℂ)*ζ) (n+shift))
      (𝓝[<] 1) (𝓝 (∑' n : ℕ, watsonTerm c ζ (n+shift))) := by
  apply tendsto_tsum_of_dominated_convergence ((summable_nat_add_iff shift).2 (summable_norm_watsonTerm hk hζ hc))
  · intro n
    have h : ContinuousAt (fun t : ℝ => watsonTerm c ((t:ℂ)*ζ) (n+shift)) 1 := by
      unfold watsonTerm
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      simpa using prod_ne_zero_iff.mpr (fun j (_ : j ∈ Finset.range (n+shift)) =>
        watson_factor_ne_zero hk hζ hc j)
    simpa using h.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))] with t ht h0 n
    exact norm_watsonTerm_radial_le hk hζ hc hc' t h0 (le_of_lt ht) (n+shift)

end MockThetaAnalytic
