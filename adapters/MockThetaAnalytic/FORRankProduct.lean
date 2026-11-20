import FineRank
import FORRadialIdentity

/-! Fine’s rank series grouped by the parity of the smallest part. -/

noncomputable section
namespace MockThetaAnalytic
open Filter
open scoped Topology

/-- Multiplication by the distinct-parts product expresses the rank series in
terms of partitions with odd smallest part. -/
private theorem rank_odd_parts_sum (q : ℂ) (hq : ‖q‖ < 1) :
    radialPlusProduct q * radialF q = 1 + 2 * ∑' j : ℕ,
      q^(2*j+1) * ∏' n : ℕ, (1 + q^(n+(2*j+1)+1)) := by
  have hFine := radialF_eq_two_sub_fine q hq
  have hsFine := summable_rankFine q hq
  let P := radialPlusProduct q
  let D (m : ℕ) : ℂ := ∏ i ∈ Finset.range m, (1+q^(i+1))
  let T (m : ℕ) : ℂ := ∏' n : ℕ, (1+q^(n+m+1))
  let w (m : ℕ) := q^(m+1) * T (m+1)
  have nz : P ≠ 0 := (radialPochhammers_ne_zero hq).2
  have mult (m : ℕ) : Multipliable (fun n : ℕ => 1+q^(n+m+1)) :=
    Complex.multipliable_one_add_of_summable <| (summable_geometric_of_norm_lt_one hq).comp_injective
      (i := fun n => n+m+1) (by intro i j h; simpa using h)
  have hDT (m : ℕ) : D m * T m = P :=
    (mult m).prod_mul_tprod_nat_mul' (f := fun n : ℕ => 1+q^(n+1))
  have hn (m : ℕ) : D m ≠ 0 := fun h => nz (by rw [← hDT m, h, zero_mul])
  have ht (m : ℕ) : T m = P / D m := (eq_div_iff (hn m)).2 (by rw [mul_comm, hDT])
  have hlim : Tendsto T atTop (𝓝 1) := by
    have hD : Tendsto D atTop (𝓝 P) := (hasProd_radialPochhammers hq).2.tendsto_prod_nat
    simpa only [funext ht, div_self nz] using (tendsto_const_nhds (x := P)).div hD nz
  have hs : Summable w := by
    obtain ⟨B,hB⟩ := hlim.norm.bddAbove_range
    apply ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right B).of_norm_bounded
    intro m
    rw [show ‖w m‖ = ‖q‖^(m+1)*‖T (m+1)‖ by simp [w, norm_pow]]
    apply mul_le_mul (pow_le_pow_of_le_one (norm_nonneg q) hq.le (Nat.le_succ m))
        (hB ⟨m+1, rfl⟩) (norm_nonneg _) (by positivity)
  have hw (m : ℕ) : w m = T m - T (m+1) := by
    have h : T m = (1+q^(m+1)) * T (m+1) := by
      apply (mul_left_cancel₀ (hn m))
      rw [hDT, ← mul_assoc, ← hDT (m+1)]
      simp [D, Finset.prod_range_succ]
    rw [h]
    dsimp [w]
    ring
  have h0 : T 0 = P := by simp [T, P, radialPlusProduct]
  have hsum : ∑' m, w m = P - 1 := by
    apply HasSum.tsum_eq
    apply hs.hasSum_iff_tendsto_nat.2
    simpa only [funext hw, Finset.sum_range_sub', h0] using
      (tendsto_const_nhds (x := P)).sub hlim
  let v (m : ℕ) := (-1:ℂ)^m * w m
  have hsv : Summable v := hs.norm.of_norm_bounded (by intro m; simp [v, norm_pow])
  have hpf : P * radialF q = P + ∑' m, v m := by
    rw [hFine, mul_sub, ← hsFine.tsum_mul_left, (hsFine.mul_left P).tsum_eq_zero_add]
    have hsuc (m : ℕ) : P * ((-q)^(m+1)/D (m+1)) = -v m := by
      rw [show P = D (m+1)*T (m+1) from (hDT _).symm, neg_eq_neg_one_mul q, mul_pow]
      dsimp [v, w]
      rw [pow_succ (-1:ℂ)]
      field_simp [hn]
    change P * 2 - (P*( (-q)^0 / D 0) + ∑' m : ℕ, P*((-q)^(m+1)/D (m+1))) = _
    simp only [funext hsuc, tsum_neg, pow_zero, show D 0 = 1 by simp [D], div_one, mul_one]
    ring
  have split (f : ℕ → ℂ) (hf : Summable f) :=
    tsum_even_add_odd (f := f)
      (hf.comp_injective (i := fun k : ℕ => 2*k) (by intro i j h; dsimp at h; omega))
      (hf.comp_injective (i := fun k : ℕ => 2*k+1) (by intro i j h; dsimp at h; omega))
  have hwpar := split w hs
  have hvpar := split v hsv
  have hve (k : ℕ) : v (2*k) = w (2*k) := by simp [v, pow_mul]
  have hvo (k : ℕ) : v (2*k+1) = -w (2*k+1) := by simp [v, pow_succ, pow_mul]
  simp only [funext hve, funext hvo, tsum_neg] at hvpar
  change P * radialF q = 1+2*∑' j, w (2*j)
  linear_combination hpf - hvpar - hwpar - hsum

/-- The odd and even tails above the odd exponent 2j+1 combine into the
ordinary product whose first exponent is 2j+2. -/
private theorem watsonOddTerm_eq_tail (q : ℂ) (hq : ‖q‖ < 1) (j : ℕ) :
    watsonOddTail q (j+1) * watsonEvenTail q j = ∏' n : ℕ, (1 + q^(n+(2*j+1)+1)) := by
  let f (n : ℕ) := 1+q^(n+(2*j+1)+1)
  have he : HasProd (fun n : ℕ => f (2*n)) (watsonEvenTail q j) := by
    apply (watsonEvenTail_hasProd hq j).congr_fun
    intro n
    dsimp [f]
    congr 2
    omega
  have ho : HasProd (fun n : ℕ => f (2*n+1)) (watsonOddTail q (j+1)) := by
    apply (watsonOddTail_hasProd hq (j+1)).congr_fun
    intro n
    dsimp [f]
    congr 2
    omega
  rw [mul_comm]
  exact (he.even_mul_odd (f := f) ho).tprod_eq.symm

/-- The rank and Watson series share the generating function for distinct
partitions with odd smallest part. -/
theorem radialPlus_mul_radialF (q : ℂ) (hq : ‖q‖ < 1) :
    radialPlusProduct q * radialF q = 1 + 2 * watsonA q 0 := by
  rw [rank_odd_parts_sum q hq, watsonA]
  simp only [Nat.zero_mul, Nat.zero_add, mul_assoc, watsonOddTerm_eq_tail q hq]

end MockThetaAnalytic
