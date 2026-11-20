import EichlerBridge
import Order34Source
import ThirdOrderTaylor

/-! Consequences of the proved Eichler transformation at the two reflected
cusps. The finite endpoint and source-bound packet identities use the one
proved equation. Passing from the interior f series to its radial boundary
continues to use the Folsom–Ono–Rhoades compensated limit. -/

noncomputable section

namespace MockThetaAnalytic

open Complex Filter KElimination.QuantumRadial Order34Source
open scoped Topology

/-- Recover the finite order-34 boundary value from its actual theta period
and the order-10 boundary value. -/
theorem boundary34_from_period_and_ten_unconditional :
    boundaryValue 17 (integerNome (1/34)) =
      (fktyVerticalPeriod fktyTheta (-1/24) (-1/34) +
        (Real.sqrt (17/5) : ℂ) *
          ((fktyScale * integerNome (-1/240)) * boundaryValue 5 (integerNome (1/10)))) /
        (fktyScale * integerNome (-1/816)) := by
  have h := fkty_defect34_eq_period
  rw [fktyPhi_neg_one_div_34, fktyPhi_neg_one_div_10] at h
  have hs : fktyScale ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (mul_ne_zero (by norm_num : (12 : ℂ) ≠ 0) I_ne_zero))
  apply (eq_div_iff (mul_ne_zero hs (Complex.exp_ne_zero _))).2
  rw [mul_comm]
  exact sub_eq_iff_eq_add.mp h

/-- Removing the observed phases from the two complete packet arrays of any
signed source gives the period of the differential shadow. -/
theorem normalizedPacketDefect_eq_period_unconditional (X : ℤ) (N34 N10 : ℕ)
    (h34 : 17 ≤ N34) (h10 : 5 ≤ N10) :
    normalizedPacketDefect N34 N10 (observe X) =
      fktyVerticalPeriod (fun u => xiHalf mockCompletion (u/24) / 2) (-1/24) (-1/34) :=
  (normalizedPacketDefect_eq_period_iff X N34 N10 h34 h10).2 fkty_defect34_eq_period

/-- Along any admissible radial approach, compensated f packets converge to
the solved order-34 value once the FOR radial limit of f is supplied. -/
theorem fPackets34_tendsto_order10_period_of_FOR
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1)
    (hrlim : Tendsto r atTop (𝓝[<] (1 : ℝ)))
    (hFOR : Tendsto (fun t : ℝ => radialF ((t : ℂ)*integerNome (1/34)) +
      radialB ((t : ℂ)*integerNome (1/34))) (𝓝[<] (1 : ℝ))
        (𝓝 (boundaryValue 17 (integerNome (1/34))))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Tendsto (fun j => fPacketAtRadius (N j) 510510 (r j) (integerNome (1/34)) +
        radialB ((r j : ℂ) * integerNome (1/34))) atTop
        (𝓝 ((fktyVerticalPeriod fktyTheta (-1/24) (-1/34) +
          (Real.sqrt (17/5) : ℂ) *
            ((fktyScale * integerNome (-1/240)) * boundaryValue 5 (integerNome (1/10)))) /
          (fktyScale * integerNome (-1/816)))) := by
  rw [← boundary34_from_period_and_ten_unconditional]
  have hz : IsPrimitiveRoot (integerNome (1/34)) 34 := by
    simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 34 (by decide)
  have hsign : (-1 : ℂ)^17 = -1 := by norm_num
  simpa only [hsign, neg_one_mul, sub_neg_eq_add] using
    for_limit_from_f_packets_of_radial_law _ 17 510510 hz (by decide) (by decide) r hr hrlim
      (by simpa only [hsign, neg_one_mul, sub_neg_eq_add] using hFOR)

end MockThetaAnalytic
