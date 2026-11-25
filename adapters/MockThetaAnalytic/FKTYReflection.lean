import BoundaryValues34
import FORCyclotomicBlock

/-! FKTY's finite reflection for the crank parameter −1. The cyclic
polynomial satisfies a first-order recurrence on the nome powers. One zero
factor terminates the recurrence at the halfway power. -/

noncomputable section
namespace MockThetaAnalytic

open Complex Finset KElimination.QuantumRadial KElimination.ResidueSeries

private def reflectedProduct (v x : ℂ) (n : ℕ) : ℂ := ∏ j ∈ range n, (x+v^(j+1))

private def reflectedSum (v x : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, (-1:ℂ)^(n+1)*reflectedProduct v x n

private theorem reflectedProduct_shift (v x : ℂ) (n : ℕ) :
    reflectedProduct v (v*x) (n+1) = v^(n+1)*(x+1)*reflectedProduct v x n := by
  unfold reflectedProduct
  calc
    _ = ∏ j ∈ range (n+1), v*(x+v^j) := by
      apply prod_congr rfl
      intro j _
      rw [pow_succ' v j, mul_add]
    _ = _ := by
      rw [prod_mul_distrib, prod_const, card_range, prod_range_succ']
      simp only [pow_zero]
      ring

private theorem reflectedSum_shift (v x : ℂ) (m : ℕ)
    (hzero : (x+1)*reflectedProduct v x m = 0) :
    reflectedSum v (v*x) (m+1) = (1+x)^2*reflectedSum v x (m+1)+x := by
  let a (n : ℕ) : ℂ := (-1:ℂ)^n*reflectedProduct v x n
  have ha (n : ℕ) : v^(n+1)*a n = -a (n+1)-x*a n := by
    simp only [a, reflectedProduct, prod_range_succ, pow_succ (-1:ℂ)]
    ring
  have h0 : a 0 = 1 := by simp [a, reflectedProduct]
  have hsum : reflectedSum v x (m+1) = -(∑ n ∈ range (m+1), a n) := by
    rw [reflectedSum, ← sum_neg_distrib]
    apply sum_congr rfl
    intro n _
    simp [a, pow_succ (-1:ℂ)]
  have hshift : reflectedSum v (v*x) (m+1) =
      -1+(x+1)*∑ n ∈ range m, v^(n+1)*a n := by
    rw [reflectedSum, sum_range_succ']
    have he : (∑ n ∈ range m, (-1:ℂ)^(n+1+1)*reflectedProduct v (v*x) (n+1)) =
        ∑ n ∈ range m, (x+1)*(v^(n+1)*a n) := by
      apply sum_congr rfl
      intro n _
      rw [reflectedProduct_shift, pow_succ (-1:ℂ), pow_succ (-1:ℂ)]
      dsimp [a]
      ring
    rw [he, ← mul_sum]
    simp [reflectedProduct]
    ring
  have ht : (∑ n ∈ range m, a (n+1)) = (∑ n ∈ range (m+1), a n)-1 := by
    rw [sum_range_succ' a, h0]; ring
  have hs : (∑ n ∈ range m, a n) = (∑ n ∈ range (m+1), a n)-a m := by
    rw [sum_range_succ]; ring
  have hlast : (x+1)*a m = 0 := by
    dsimp [a]
    rw [mul_left_comm, hzero, mul_zero]
  rw [hshift, hsum]
  simp_rw [ha]
  rw [sum_sub_distrib, sum_neg_distrib, ← mul_sum, ht, hs]
  linear_combination x*hlast

private theorem reflectedProduct_at_one (v : ℂ) (n : ℕ) :
    reflectedProduct v 1 n = pochhammer (-v) v n := by
  induction n with
  | zero => simp [reflectedProduct, pochhammer]
  | succ n ih =>
    rw [reflectedProduct, prod_range_succ, ← reflectedProduct, ih, pochhammer, pow_succ' v n]
    ring

/-- The finite strange value at the reflected nome equals the unimodal
packet polynomial whenever q has halfway power −1. -/
theorem fNegPartial_reflection {q : ℂ} {k : ℕ} (hk : 0 < k) (hq : q^k = -1) :
    fNegPartial k q⁻¹ = uPartial k q := by
  have hq0 : q ≠ 0 := by intro h; simp [h, hk.ne'] at hq
  let C (x : ℂ) := reflectedSum q⁻¹ x (2*k-1+1)
  have hstep (n : ℕ) (hn : n < k) : C (q^n) = (1+q^(n+1))^2*C (q^(n+1))+q^(n+1) := by
    have hf (j : ℕ) (hj : n+1+j=k) : q^(n+1)+(q⁻¹)^j = 0 := by
      apply (mul_left_cancel₀ (pow_ne_zero j hq0) : q^j * _ = q^j * 0 → _)
      rw [mul_add, ← pow_add, add_comm j, hj, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, mul_zero]
      rw [hq]; ring
    have hz : (q^(n+1)+1)*reflectedProduct q⁻¹ (q^(n+1)) (2*k-1) = 0 := by
      by_cases h : n+1=k
      · simp [h, hq]
      · have hindex : k-(n+1)-1 < 2*k-1 := by omega
        have he : n+1+(k-(n+1)-1+1)=k := by omega
        unfold reflectedProduct
        rw [Finset.prod_eq_zero (mem_range.mpr hindex) (hf _ he), mul_zero]
    have h := reflectedSum_shift q⁻¹ (q^(n+1)) (2*k-1) hz
    rw [pow_succ' q n, inv_mul_cancel_left₀ hq0] at h
    simpa only [C, pow_succ' q n] using h
  have htel (n : ℕ) (hn : n ≤ k) : C 1 = uPartial n q+uProduct q n*C (q^n) := by
    induction n with
    | zero => simp [uPartial, uPolynomial, sumBelow, uProduct]
    | succ n ih =>
      rw [ih (by omega), hstep n (by omega)]
      simp only [uPartial, uPolynomial, sumBelow_succ, uProduct]
      ring
  have hC : C 1 = fNegPartial (2*k-1+1) q⁻¹ := by
    unfold C reflectedSum fNegPartial
    simp_rw [reflectedProduct_at_one]
    generalize 2*k-1+1 = N
    induction N with
    | zero => simp [sumBelow]
    | succ n ih => rw [sum_range_succ, sumBelow_succ, ih]
  have hinv : (q⁻¹)^k = -1 := by rw [inv_pow, hq]; norm_num
  have htruncate : fNegPartial (2*k-1+1) q⁻¹ = fNegPartial k q⁻¹ := by
    unfold fNegPartial
    apply sumBelow_eq_of_tail_zero _ _ _ (by omega)
    intro n hn _
    have h := uProduct_zero_of_le q⁻¹ k n hk hinv hn
    rw [uProduct_eq_pochhammer] at h
    rw [eq_zero_of_pow_eq_zero h, mul_zero]
  have h := htel k le_rfl
  rw [hC, htruncate, uProduct_zero_of_le q k k hk hq le_rfl, zero_mul, add_zero] at h
  exact h

/-- FKTY's normalizing phase carries the reflected FOR value at every
rational argument of even reduced denominator. -/
theorem fktyPhi_reflected_boundary (x : ℚ) {k : ℕ} (hden : x.den = 2*k) :
    fktyPhi x = (fktyScale*integerNome ((x:ℂ)/24))*boundaryValue k (integerNome (-(x:ℂ))) := by
  have hk : 0 < k := by have := x.den_pos; omega
  have hroot : IsPrimitiveRoot (integerNome (-(x:ℂ))) (2*k) := by
    simpa only [Rat.cast_neg, Rat.neg_den, hden, integerNome] using Complex.isPrimitiveRoot_exp_rat (-x)
  unfold fktyPhi
  rw [show x.den/2=k by omega,
    show integerNome (x:ℂ) = (integerNome (-(x:ℂ)))⁻¹ by simp [integerNome, mul_neg, Complex.exp_neg],
    fNegPartial_reflection hk (primitive_even_half_power hk hroot), boundaryValue]
  ring

end MockThetaAnalytic
