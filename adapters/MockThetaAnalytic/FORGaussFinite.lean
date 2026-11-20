import MockHolomorphic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination

/-! The finite, symmetric Jacobi product identity underlying the Gauss product.
The Gaussian coefficients are finite Euler-product ratios in the open disk. -/

noncomputable section
namespace MockThetaAnalytic

/-- The finite Euler product (q;q)ₙ. -/
def gaussEuler (q : ℂ) (n : ℕ) : ℂ := ∏ j ∈ Finset.range n, (1-q^(j+1))

/-- Gaussian coefficient [2n choose n+k] evaluated inside the unit disk. -/
def gaussWeight (Q : ℂ) (n k : ℕ) : ℂ :=
  if k ≤ n then gaussEuler Q (2*n) / (gaussEuler Q (n+k)*gaussEuler Q (n-k)) else 0

private def chooseQ (Q : ℂ) (n k : ℕ) : ℂ :=
  if k ≤ n then gaussEuler Q n / (gaussEuler Q k * gaussEuler Q (n-k)) else 0

private theorem euler_succ (Q : ℂ) (n : ℕ) :
    gaussEuler Q (n+1) = gaussEuler Q n * (1-Q^(n+1)) := by simp [gaussEuler, Finset.prod_range_succ]

theorem gaussEuler_ne_zero {Q : ℂ} (hQ : ‖Q‖ < 1) (n : ℕ) : gaussEuler Q n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _ h
  have he : Q^(j+1) = 1 := (sub_eq_zero.mp h).symm
  have hn := pow_lt_one₀ (norm_nonneg Q) hQ (Nat.succ_ne_zero j)
  rw [← Complex.norm_pow, he, norm_one] at hn
  exact lt_irrefl _ hn

private theorem chooseQ_zero {Q : ℂ} (hQ : ‖Q‖ < 1) (n : ℕ) :
    chooseQ Q n 0 = 1 := by
  simp [chooseQ, show gaussEuler Q 0 = 1 by simp [gaussEuler], gaussEuler_ne_zero hQ]

private theorem chooseQ_diag {Q : ℂ} (hQ : ‖Q‖ < 1) (n : ℕ) :
    chooseQ Q n n = 1 := by
  simp [chooseQ, show gaussEuler Q 0 = 1 by simp [gaussEuler], gaussEuler_ne_zero hQ]

private theorem chooseQ_next {Q : ℂ} (hQ : ‖Q‖ < 1) {n k : ℕ} (hk : k ≤ n) :
    chooseQ Q (n+1) (k+1) = chooseQ Q n (k+1) + Q^(n-k) * chooseQ Q n k := by
  rcases eq_or_lt_of_le hk with rfl | hlt
  · rw [chooseQ_diag hQ, chooseQ_diag hQ]
    simp [chooseQ]
  · obtain ⟨d, rfl⟩ : ∃ d, n = k+1+d := by exact ⟨n-(k+1), by omega⟩
    simp only [chooseQ, show k+1 ≤ k+1+d+1 by omega, show k+1 ≤ k+1+d by omega,
      show k ≤ k+1+d by omega, if_true, show k+1+d+1-(k+1)=d+1 by omega,
      show k+1+d-(k+1)=d by omega, show k+1+d-k=d+1 by omega]
    have hz (m : ℕ) : 1-Q^(m+1) ≠ 0 := by
      intro he
      have hn := pow_lt_one₀ (norm_nonneg Q) hQ (Nat.succ_ne_zero m)
      rw [← Complex.norm_pow, ← sub_eq_zero.mp he, norm_one] at hn
      exact lt_irrefl _ hn
    rw [euler_succ Q (k+1+d), euler_succ Q k, euler_succ Q d,
      show k+1+d+1 = (k+1)+(d+1) by omega, pow_add]
    field_simp [hz, gaussEuler_ne_zero hQ]
    ring

private def coeff (q x : ℂ) (n k : ℕ) := (-x)^k*q^(k^2)*chooseQ (q^2) n k

private theorem coeff_succ {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) {n k : ℕ} (hk : k ≤ n) :
    coeff q x (n+1) (k+1) = coeff q x n (k+1) - x*q^(2*n+1)*coeff q x n k := by
  have hQ : ‖q^2‖ < 1 := by rw [Complex.norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by decide : 2 ≠ 0)
  unfold coeff
  rw [chooseQ_next hQ hk, ← pow_mul]
  have hp : q^((k+1)^2)*q^(2*(n-k)) = q^(2*n+1)*q^(k^2) := by
    rw [← pow_add, ← pow_add]
    congr 1
    nlinarith [Nat.sub_add_cancel hk]
  rw [pow_succ (-x) k]
  linear_combination (-x)^k*(-x)*chooseQ (q^2) n k*hp

private theorem gaussian_expansion {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) (n : ℕ) :
    (∏ j ∈ Finset.range n, (1-x*q^(2*j+1))) = ∑ k ∈ Finset.range (n+1), coeff q x n k := by
  have hQ : ‖q^2‖ < 1 := by rw [Complex.norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by decide : 2 ≠ 0)
  have hz (i : ℕ) : coeff q x i 0 = 1 := by simp [coeff, chooseQ_zero hQ]
  induction n with
  | zero => simp [hz]
  | succ n ih =>
    have htop : coeff q x n (n+1) = 0 := by simp [coeff, chooseQ]
    have hsum : (∑ k ∈ Finset.range (n+1), coeff q x n (k+1)) + 1 =
        ∑ k ∈ Finset.range (n+1), coeff q x n k := by
      calc
        _ = ∑ k ∈ Finset.range (n+2), coeff q x n k := by rw [Finset.sum_range_succ' (n := n+1) (coeff q x n), hz]
        _ = _ := by rw [Finset.sum_range_succ, htop, add_zero]
    rw [Finset.prod_range_succ, ih, Finset.sum_range_succ' (n := n+1), hz]
    rw [Finset.sum_congr rfl (fun k hk => coeff_succ hq x (Nat.le_of_lt_succ (Finset.mem_range.mp hk))),
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    linear_combination -hsum

private def xshift (q : ℂ) (n : ℕ) := q^(-(2*(n : ℤ)))
private def scale (q : ℂ) (n : ℕ) := (-1 : ℂ)^n*q^(n^2)

private theorem scaled_negative_factors (q : ℂ) (hq0 : q ≠ 0) (n : ℕ) :
    scale q n * (∏ j ∈ Finset.range n, (1-(q^(2*j+1))⁻¹)) =
      ∏ j ∈ Finset.range n, (1-q^(2*j+1)) := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have hstep : -q^(2*n+1)*(1-(q^(2*n+1))⁻¹) = 1-q^(2*n+1) := by
      field_simp [hq0]
      ring
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← hstep, ← ih]
    simp only [scale, pow_succ (-1 : ℂ), show (n+1)^2=n^2+(2*n+1) by ring, pow_add]
    ring

private theorem scaled_product (q : ℂ) (hq0 : q ≠ 0) (n : ℕ) :
    scale q n * (∏ j ∈ Finset.range (2*n), (1-xshift q n*q^(2*j+1))) =
      (∏ j ∈ Finset.range n, (1-q^(2*j+1)))^2 := by
  have up (j : ℕ) : xshift q n*q^(2*(n+j)+1) = q^(2*j+1) := by
    unfold xshift
    rw [← zpow_natCast q (2*(n+j)+1), ← zpow_add₀ hq0, ← zpow_natCast q (2*j+1)]
    congr 1
    push_cast
    ring
  have low (j : ℕ) (hj : j<n) : xshift q n*q^(2*(n-1-j)+1) = (q^(2*j+1))⁻¹ := by
    unfold xshift
    rw [← zpow_natCast q (2*(n-1-j)+1), ← zpow_add₀ hq0,
      ← zpow_natCast q (2*j+1), ← zpow_neg]
    congr 1
    push_cast
    omega
  rw [two_mul, Finset.prod_range_add, ← Finset.prod_range_reflect (fun j => 1-xshift q n*q^(2*j+1)) n]
  simp_rw [up]
  rw [Finset.prod_congr rfl (fun j hj => congrArg (fun z : ℂ => 1-z) (low j (Finset.mem_range.mp hj))),
    ← mul_assoc, scaled_negative_factors q hq0, sq]

private theorem scaled_coeff (q : ℂ) (hq0 : q ≠ 0) (n k : ℕ) :
    scale q n * coeff q (xshift q n) (2*n) k =
    (-1 : ℂ)^(n+k)*q^(((k : ℤ)-n)^2)*chooseQ (q^2) (2*n) k := by
  have hq : q^(n^2)*(xshift q n)^k*q^(k^2) = q^(((k : ℤ)-n)^2) := by
    unfold xshift
    rw [← zpow_natCast q (n^2), ← zpow_natCast (q^_) k, ← zpow_mul,
      ← zpow_natCast q (k^2), ← zpow_add₀ hq0, ← zpow_add₀ hq0]
    congr 1
    push_cast
    ring
  rw [← hq, pow_add]
  simp only [scale, coeff, neg_eq_neg_one_mul (xshift q n), mul_pow]
  ring

private def binTerm (q : ℂ) (n k : ℕ) :=
  (-1 : ℂ)^k*q^(k^2)*gaussWeight (q^2) n k

private theorem scaled_coeff_high (q : ℂ) (hq0 : q ≠ 0) (n k : ℕ) (hk : k ≤ n) :
    scale q n * coeff q (xshift q n) (2*n) (n+k) = binTerm q n k := by
  rw [scaled_coeff q hq0]
  have hb : chooseQ (q^2) (2*n) (n+k) = gaussWeight (q^2) n k := by
    simp only [chooseQ, gaussWeight, if_pos hk, if_pos (show n+k ≤ 2*n by omega),
      show 2*n-(n+k)=n-k by omega]
  rw [hb, show n+(n+k)=2*n+k by omega, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [Nat.cast_add, add_sub_cancel_left, ← Nat.cast_pow, zpow_natCast]
  rfl

private theorem scaled_coeff_low (q : ℂ) (hq0 : q ≠ 0) (n k : ℕ) (hk : k ≤ n) :
    scale q n * coeff q (xshift q n) (2*n) (n-k) = binTerm q n k := by
  rw [scaled_coeff q hq0]
  have hb : chooseQ (q^2) (2*n) (n-k) = gaussWeight (q^2) n k := by
    simp only [chooseQ, gaussWeight, if_pos hk, if_pos (show n-k ≤ 2*n by omega),
      show 2*n-(n-k)=n+k by omega]
    rw [mul_comm (gaussEuler (q^2) (n-k))]
  rw [hb, show n+(n-k)=2*(n-k)+k by omega, pow_add, pow_mul, neg_one_sq, one_pow, one_mul,
    Nat.cast_sub hk, show (n : ℤ)-k-n = -(k : ℤ) by ring, neg_sq]
  rw [← Nat.cast_pow, zpow_natCast]
  rfl

/-- The symmetric finite Jacobi identity, before taking any infinite
product or bilateral-series limit. Each noncentral term occurs twice. -/
theorem gauss_finite (q : ℂ) (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ) :
    (∏ j ∈ Finset.range n, (1-q^(2*j+1)))^2 = gaussWeight (q^2) n 0 +
      2 * ∑ k ∈ Finset.range n, (-1 : ℂ)^(k+1)*q^((k+1)^2)*gaussWeight (q^2) n (k+1) := by
  rw [← scaled_product q hq0, gaussian_expansion hq, Finset.mul_sum,
    show 2*n+1=n+(n+1) by omega, Finset.sum_range_add]
  let c (k : ℕ) := scale q n * coeff q (xshift q n) (2*n) k
  change ∑ k ∈ Finset.range n, c k + ∑ k ∈ Finset.range (n+1), c (n+k) = _
  have low : (∑ k ∈ Finset.range n, c k) = ∑ k ∈ Finset.range n, binTerm q n (k+1) := by
    rw [← Finset.sum_range_reflect c n]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show n-1-k = n-(k+1) by omega]
    exact scaled_coeff_low q hq0 n (k+1) (Finset.mem_range.mp hk)
  have high : (∑ k ∈ Finset.range (n+1), c (n+k)) = ∑ k ∈ Finset.range (n+1), binTerm q n k :=
    Finset.sum_congr rfl (fun k hk => scaled_coeff_high q hq0 n k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  rw [low, high, Finset.sum_range_succ' (binTerm q n)]
  have hzero : binTerm q n 0 = gaussWeight (q^2) n 0 := by simp [binTerm]
  rw [hzero]
  unfold binTerm
  ring

end MockThetaAnalytic
