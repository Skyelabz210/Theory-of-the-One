import ThirdOrderRows
import MockHolomorphic
import QuantumTransport34

/-! The integer coefficients of third-order f sum to its defining hypergeometric
series for |q| < 1. Absolute convergence of the joint series validates collecting
its signed summands by degree. This supplies the Taylor input for the
order-34 packet limit. -/

noncomputable section

namespace MockThetaAnalytic

open Filter KElimination MockTheta QuantumRadial CoefficientEvaluation
open scoped Topology

private theorem norm_shift_row (a : ℕ → ℤ) (j : ℕ) (q : ℂ)
    (ha : Summable (fun d => ‖weighted a q d‖)) :
    HasSum (fun d => ‖weighted (shift j a) q d‖) (‖q‖^j * ∑' d, ‖weighted a q d‖) := by
  have hz : ∑ d ∈ Finset.range j, ‖weighted (shift j a) q d‖ = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    simp [weighted, shift, if_neg (Nat.not_le_of_lt (Finset.mem_range.mp hd))]
  rw [← add_zero (‖q‖^j * _), ← hz, ← hasSum_nat_add_iff]
  apply (ha.hasSum.mul_left (‖q‖^j)).congr_fun
  intro d
  simp [weighted, shift, pow_add, norm_pow]
  ring

private theorem weighted_row_bound (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    r^(n*n) * (∏ j ∈ Finset.range n, (1-r^(j+1))^2)⁻¹ ≤ mockSquareBound r n := by
  have hD : ((1-r)^2)^n ≤ ∏ j ∈ Finset.range n, (1-r^(j+1))^2 := by
    calc
      _ = ∏ _j ∈ Finset.range n, (1-r)^2 := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => sq_nonneg _) (fun j _ => pow_le_pow_left₀
        (sub_nonneg.mpr hr1.le) (sub_le_sub_left (pow_le_of_le_one hr hr1.le (Nat.succ_ne_zero j)) 1) 2)
  rw [← div_eq_mul_inv, mockSquareBound, div_pow, ← pow_mul]
  exact div_le_div_of_nonneg_left (pow_nonneg hr _) (pow_pos (pow_pos (sub_pos.mpr hr1) _) _) hD

/-- Ramanujan's actual signed coefficient recurrence gives the Taylor expansion
of radialF throughout the open disk. -/
theorem hasSum_radialF_coefficients (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun d => complexFCoeff d * q^d) (radialF q) := by
  let rows (n : ℕ) : ℕ → ℤ := inverseSquaredPochhammer n
  let a (n : ℕ) := shift (n*n) (rows n)
  have hs (n : ℕ) := norm_shift_row (rows n) (n*n) q (thirdOrderRowNorm q hq n).1
  have hsum : Summable (fun n => ‖q‖^(n*n) * ∑' d, ‖weighted (rows n) q d‖) := by
    apply (summable_mockSquareBound (norm_nonneg q) hq).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _)
      (tsum_nonneg fun d => norm_nonneg _))]
    apply le_trans (mul_le_mul_of_nonneg_left (thirdOrderRowNorm q hq n).2 (pow_nonneg (norm_nonneg q) _))
    exact weighted_row_bound ‖q‖ (norm_nonneg q) hq n
  have habs : Summable (fun p : ℕ×ℕ => ‖weighted (a p.1) q p.2‖) := by
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
    exact ⟨fun n => (hs n).summable, hsum.congr (fun n => (hs n).tsum_eq.symm)⟩
  have hvalue (n : ℕ) : HasSum (weighted (a n) q) (radialFTerm n q) := by
    simpa only [a, rows, radialFTerm, div_eq_mul_inv] using
      eval_shift (rows n) q _ (n*n) (thirdOrderRow q hq n)
  exact hasSum_shifted_family (fun n => n*n) Nat.le_mul_self rows q (fun n => radialFTerm n q)
    hvalue habs.of_norm

private theorem hasSum_interior_radius {ζ : ℂ} {b : ℕ} (hz : IsPrimitiveRoot ζ b) (hb : b ≠ 0)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    HasSum (fun d => complexFCoeff d * ((t : ℂ)*ζ)^d) (radialF ((t : ℂ)*ζ)) := by
  apply hasSum_radialF_coefficients
  rwa [norm_mul, hz.norm'_eq_one hb, mul_one, Complex.norm_of_nonneg ht.le]

/-- At any primitive even cusp, an admitted positive period and the FOR radial
law suffice for compensated Taylor packets along the given radial approach. -/
theorem for_limit_from_f_packets_of_radial_law (ζ : ℂ) (k L : ℕ)
    (hζ : IsPrimitiveRoot ζ (2*k)) (hL : 0 < L) (hperiod : 2*k ∣ L)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1) (hlim : Tendsto r atTop (𝓝[<] (1 : ℝ)))
    (hFOR : Tendsto (fun t : ℝ => radialF ((t : ℂ)*ζ) - (-1 : ℂ)^k * radialB ((t : ℂ)*ζ))
      (𝓝[<] (1 : ℝ)) (𝓝 (boundaryValue k ζ))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Tendsto (fun j => fPacketAtRadius (N j) L (r j) ζ - (-1 : ℂ)^k * radialB ((r j : ℂ)*ζ))
        atTop (𝓝 (boundaryValue k ζ)) :=
  for_limit_from_f_packets ζ k L hζ hL hperiod r hr hlim
    (hasSum_interior_radius hζ (ne_zero_of_dvd_ne_zero hL.ne' hperiod)) hFOR

/-- The interior Taylor expansion has been proved. At the order-34 cusp the
remaining analytic inputs are the FOR radial limit and the FKTY weight-half law. -/
theorem fPackets34_tendsto_order10_period_of_radial_laws (hFKTY : FKTYWeightHalfLaw)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1)
    (hrlim : Filter.Tendsto r Filter.atTop (𝓝[<] (1 : ℝ)))
    (hFOR : Filter.Tendsto (fun t : ℝ => radialF ((t : ℂ)*integerNome (1/34)) +
      radialB ((t : ℂ)*integerNome (1/34))) (𝓝[<] (1 : ℝ))
        (𝓝 (boundaryValue 17 (integerNome (1/34))))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Filter.Tendsto (fun j => fPacketAtRadius (N j) 510510 (r j) (integerNome (1/34)) +
        radialB ((r j : ℂ) * integerNome (1/34))) Filter.atTop
        (𝓝 ((fktyVerticalPeriod fktyTheta (-1/24) (-1/34) +
          (Real.sqrt (17/5) : ℂ) *
            ((fktyScale * integerNome (-1/240)) * boundaryValue 5 (integerNome (1/10)))) /
          (fktyScale * integerNome (-1/816)))) := by
  apply fPackets34_tendsto_order10_period hFKTY r hr hrlim _ hFOR
  have hz : IsPrimitiveRoot (integerNome (1/34)) 34 := by
    simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 34 (by decide)
  exact hasSum_interior_radius hz (by decide)

end MockThetaAnalytic
