import FKTYTheta
import GaussianPairIntegrable

/-! On the vertical ray above −1/24 the quadratic phases of the FKTY theta
series are antiperiodic with shift 144. Shifting the convergent series once
expresses its value as a finite head plus paired Gaussian differences. -/

noncomputable section

namespace MockThetaAnalytic

open Complex KElimination.MockThetaShadow KElimination.ShadowConvergence

/-- The signed coefficient of the Gaussian at the cusp −1/24. -/
def fktyCuspPhase (m : ℕ) : ℂ :=
  (shadowSign m : ℂ) * exp (-(m : ℂ)^2 * (2 * Real.pi * I) / 576)

theorem norm_fktyCuspPhase_le_one (m : ℕ) : ‖fktyCuspPhase m‖ ≤ 1 := by
  have h : (-(m : ℂ)^2 * (2 * Real.pi * I) / 576).re = 0 := by
    rw [show -(m : ℂ)^2 * (2 * Real.pi * I) / 576 =
      ((-(m : ℝ)^2 * (2 * Real.pi) / 576 : ℝ) : ℂ) * I by push_cast; ring]
    simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  simp only [fktyCuspPhase, norm_mul, Complex.norm_exp, h, Real.exp_zero, mul_one]
  unfold shadowSign
  split_ifs <;> norm_num

theorem fktyCuspPhase_add_144 (m : ℕ) : fktyCuspPhase (m+144) = -fktyCuspPhase m := by
  have hsign : shadowSign (m+144) = shadowSign m := by simp [shadowSign, Nat.add_mod]
  unfold fktyCuspPhase
  rw [hsign]
  by_cases hz : shadowSign m = 0
  · simp [hz]
  have ho : Odd m := Nat.odd_iff.mpr (by
    unfold shadowSign at hz
    split_ifs at hz <;> omega)
  obtain ⟨k, rfl⟩ := ho
  have he (n : ℕ) :
      exp (-((2*n+1+144 : ℕ) : ℂ)^2 * (2 * Real.pi * I) / 576) =
        -exp (-((2*n+1 : ℕ) : ℂ)^2 * (2 * Real.pi * I) / 576) := by
    have harg : -((2*n+1+144 : ℕ) : ℂ)^2 * (2 * Real.pi * I) / 576 =
        -((2*n+1 : ℕ) : ℂ)^2 * (2 * Real.pi * I) / 576 + Real.pi * I -
          ((n+37 : ℕ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [harg, Complex.exp_sub, Complex.exp_add, Complex.exp_pi_mul_I,
      Complex.exp_nat_mul_two_pi_mul_I]
    ring
  rw [he, mul_neg]

theorem shadowTerm_cusp (t : ℝ) (m : ℕ) :
    shadowTerm (shadowNome ((-1/24 : ℂ) + (t : ℂ)*I)) m =
      fktyCuspPhase m * (gaussianMode (Real.pi/12) m t : ℂ) := by
  unfold shadowTerm shadowNome fktyCuspPhase gaussianMode shadowWeight
  rw [← Complex.exp_nat_mul]
  push_cast
  have hexp : (m : ℂ)^2 * ((2 * Real.pi / 24 * (-1 / 24 + (t : ℂ) * I)) * I) =
      -(m : ℂ)^2 * (2 * Real.pi * I) / 576 + -(Real.pi / 12 * (m : ℂ)^2) * t := by
    ring_nf
    simp [I_sq]
    ring
  rw [hexp, Complex.exp_add]
  ring

theorem summable_fktyCuspModes (t : ℝ) (ht : 0 < t) :
    Summable (fun m => fktyCuspPhase m * (gaussianMode (Real.pi/12) m t : ℂ)) := by
  exact (shadowTerm_summable _ (norm_shadowNome_lt_one _ (by simpa using ht))).congr
    (shadowTerm_cusp t)

theorem fktyTheta_cusp (t : ℝ) (ht : 0 < t) :
    fktyTheta ((-1/24 : ℂ) + (t : ℂ)*I) =
      2 * ∑' m, fktyCuspPhase m * (gaussianMode (Real.pi/12) m t : ℂ) := by
  rw [fktyTheta_eq_shadowSeries _ (by simpa using ht), shadowSeries]
  simp_rw [shadowTerm_cusp]

/-- The head contains m=0 with zero amplitude. Each remaining difference
preserves its original complex phase; absolute convergence permits the shift. -/
theorem fktyTheta_cusp_paired (t : ℝ) (ht : 0 < t) :
    fktyTheta ((-1/24 : ℂ) + (t : ℂ)*I) =
      (∑ m ∈ Finset.range 144, fktyCuspPhase m * (gaussianMode (Real.pi/12) m t : ℂ)) +
      ∑' m, fktyCuspPhase m *
        ((gaussianMode (Real.pi/12) m t - gaussianMode (Real.pi/12) (m+144) t : ℝ) : ℂ) := by
  let f (m : ℕ) := fktyCuspPhase m * (gaussianMode (Real.pi/12) m t : ℂ)
  have hf : Summable f := summable_fktyCuspModes t ht
  have hshift : Summable (fun m => f (m+144)) := (summable_nat_add_iff 144).2 hf
  have hpair (m : ℕ) : fktyCuspPhase m *
      ((gaussianMode (Real.pi/12) m t - gaussianMode (Real.pi/12) (m+144) t : ℝ) : ℂ) =
      f m + f (m+144) := by
    simp only [f, fktyCuspPhase_add_144, Complex.ofReal_sub]
    ring
  rw [fktyTheta_cusp t ht]
  simp_rw [hpair]
  change 2 * ∑' m, f m = (∑ m ∈ Finset.range 144, f m) + ∑' m, (f m + f (m+144))
  rw [hf.tsum_add hshift]
  have h := hf.sum_add_tsum_nat_add 144
  linear_combination -h

end MockThetaAnalytic
