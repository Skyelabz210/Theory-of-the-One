import FORPhiRadial
import FORRadialProducts
import FORRadialIdentity

/-! Clearing the finite even product in Watson's third-order φ(−q).
Multiplication by (−q;q)∞ leaves every odd factor and the even factors
following the cutoff. -/

noncomputable section
namespace MockThetaAnalytic

private theorem radialPlus_eq_odd_mul_even {q : ℂ} (hq : ‖q‖ < 1) :
    radialPlusProduct q = watsonOddTail q 0 * watsonEvenTail q 0 := by
  have ho := watsonOddTail_hasProd hq 0
  have he := watsonEvenTail_hasProd hq 0
  simp only [Nat.add_zero] at ho he
  exact (HasProd.even_mul_odd (f := fun n : ℕ => 1+q^(n+1)) ho he).tprod_eq

private theorem watsonEvenTail_split {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    (∏ j ∈ Finset.range k, (1+q^(2*j+2))) * watsonEvenTail q k = watsonEvenTail q 0 := by
  have head := HasProd.prod_range_mul (f := fun n : ℕ => 1+q^(2*n+2))
    (k := k) (watsonEvenTail_hasProd hq k)
  exact head.unique (by simpa only [Nat.add_zero] using watsonEvenTail_hasProd hq 0)

private theorem evenPrefix_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    (∏ j ∈ Finset.range k, (1 + q^(2*j+2))) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ he
  have h : q^(2*i+2) = -1 := by linear_combination he
  have hlt : ‖q^(2*i+2)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  simp [h] at hlt

/-- The product-cleared Watson series in the open disk. The nth term retains
all odd factors and exactly the even tail after its first n factors. -/
theorem radialPlus_mul_watsonPhi {q : ℂ} (hq : ‖q‖ < 1) :
    radialPlusProduct q * watsonPhi q = ∑' n : ℕ,
      (-1 : ℂ)^n * q^(n*n) * watsonOddTail q 0 * watsonEvenTail q n := by
  rw [watsonPhi, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have hs : (-1 : ℂ)^(n^2) = (-1 : ℂ)^n := by
    simp [neg_one_pow_eq_ite, sq, Nat.even_mul]
  have hnum : (-q)^(n^2) = (-1 : ℂ)^n * q^(n*n) := by
    rw [← neg_one_mul q, mul_pow, hs, sq]
  rw [watsonPhiTerm, hnum, radialPlus_eq_odd_mul_even hq, ← watsonEvenTail_split hq n]
  field_simp [evenPrefix_ne_zero hq n]

end MockThetaAnalytic
