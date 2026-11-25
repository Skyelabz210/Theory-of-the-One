import FORPhiProduct
import FORRankProduct
import FORGaussLimit

/-! Watson's complementary third-order formula uses ψ(−q). Its denominator
runs over odd powers. At primitive roots of order 2k with even k, each
block of k factors doubles the denominator. -/

noncomputable section
namespace MockThetaAnalytic
open Complex Filter Finset Set
open scoped Topology

def watsonPsiTerm (q : ℂ) (n : ℕ) : ℂ :=
  (-q)^(n^2) / ∏ j ∈ range n, (1+q^(2*j+1))

/-- Ramanujan's third-order ψ evaluated at −q, starting at n=1. -/
def watsonPsi (q : ℂ) : ℂ := ∑' n : ℕ, watsonPsiTerm q (n+1)

private theorem oddPrefix_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    (∏ j ∈ range n, (1+q^(2*j+1))) ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro j _ he
  have h : q^(2*j+1) = -1 := by linear_combination he
  have hlt : ‖q^(2*j+1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  simp [h] at hlt

private theorem oddPrefix_mul_tail {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    (∏ j ∈ range n, (1+q^(2*j+1))) * watsonOddTail q n = watsonOddTail q 0 := by
  have h := HasProd.prod_range_mul (f := fun j : ℕ => 1+q^(2*j+1))
    (k := n) (watsonOddTail_hasProd hq n)
  exact h.unique (by simpa only [Nat.add_zero] using watsonOddTail_hasProd hq 0)

private theorem radialPlus_mul_watsonPsi {q : ℂ} (hq : ‖q‖ < 1) :
    radialPlusProduct q * watsonPsi q = ∑' n : ℕ,
      (-1:ℂ)^(n+1)*q^((n+1)*(n+1))*watsonEvenTail q 0*watsonOddTail q (n+1) := by
  rw [watsonPsi, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have hs : (-1 : ℂ)^((n+1)^2) = (-1 : ℂ)^(n+1) := by
    simp [neg_one_pow_eq_ite, sq, Nat.even_mul]
  have hn : (-q)^((n+1)^2) = (-1:ℂ)^(n+1)*q^((n+1)*(n+1)) := by
    rw [← neg_one_mul q, mul_pow, hs, sq]
  rw [watsonPsiTerm, hn, radialPlus_eq_odd_mul_even hq, ← oddPrefix_mul_tail hq (n+1)]
  field_simp [oddPrefix_ne_zero hq (n+1)]

/-- The complementary Watson identity on the open disk. -/
theorem watson_compensated_sub_identity (q : ℂ) (hq : ‖q‖ < 1) :
    radialF q - radialB q = -4 * watsonPsi q := by
  have hf := radialPlus_mul_radialF q hq
  have hb : radialPlusProduct q * radialB q = 2*watsonThetaHalf q-1 :=
    radialPlus_mul_radialB_eq_thetaHalf q hq
  have hp := watson_odd_product_series hq
  rw [← radialPlus_mul_watsonPsi hq] at hp
  apply mul_left_cancel₀ (radialPochhammers_ne_zero hq).2
  linear_combination hf - hb + 2*hp

theorem order24_half_power (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 24) : ζ^12 = -1 :=
  primitive_even_half_power (k := 12) (by decide) hζ

theorem order24_odd_block (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 24) (r : ℕ) :
    (∏ j ∈ range 12, (1+ζ^(2*(r+j)+1))) = 2 :=
  watson_denominator_block (k := 12) (by decide) hζ 1 (by decide) r

theorem watsonPsiTerm_add_twelve (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 24) (n : ℕ) :
    watsonPsiTerm ζ (n+12) = watsonPsiTerm ζ n / 2 :=
  watsonTerm_add_halfOrder (k := 12) (by decide) hζ (c := 1) (by decide) n

theorem watsonPsi_eq_head {ζ : ℂ} {k : ℕ} (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2*k))
    (heven : Even k) : watsonPsi ζ = 2 * (∑ n ∈ range k, watsonPsiTerm ζ n) - 1 := by
  have h : Odd (k+1) := heven.add_odd (by decide)
  have hs := (summable_norm_watsonTerm hk hζ (c := 1) h).of_norm.tsum_eq_zero_add
  rw [watsonTerm_tsum_eq_two_mul_sum hk hζ h, show watsonTerm 1 ζ 0 = 1 by simp [watsonTerm]] at hs
  unfold watsonPsi
  change (∑' n : ℕ, watsonTerm 1 ζ (n+1)) = 2 * (∑ n ∈ range k, watsonTerm 1 ζ n) - 1
  linear_combination -hs

theorem watsonPsi_eq_head24 (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 24) :
    watsonPsi ζ = 2 * (∑ n ∈ range 12, watsonPsiTerm ζ n) - 1 :=
  watsonPsi_eq_head (k := 12) (by decide) hζ (by decide)

/-- At every primitive even order with even half-order, ψ has its actual
series value as a radial limit. -/
theorem watsonPsi_radial_limit_of_even {ζ : ℂ} {k : ℕ} (hk : 0 < k)
    (hζ : IsPrimitiveRoot ζ (2*k)) (heven : Even k) :
    Tendsto (fun t : ℝ => watsonPsi ((t:ℂ)*ζ)) (𝓝[<] 1) (𝓝 (watsonPsi ζ)) := by
  exact watsonTerm_radial_limit hk hζ (c := 1) (heven.add_odd (by decide)) (by decide) 1

theorem watsonPsi_radial_limit24 (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 24) :
    Tendsto (fun t : ℝ => watsonPsi ((t:ℂ)*ζ)) (𝓝[<] 1) (𝓝 (watsonPsi ζ)) :=
  watsonPsi_radial_limit_of_even (k := 12) (by decide) hζ (by decide)

end MockThetaAnalytic
