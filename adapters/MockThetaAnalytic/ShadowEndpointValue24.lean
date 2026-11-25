import ShadowEndpoint

/-! Exact identification of the diagonal period with the terminating FKTY
value. Both expressions reduce to one integer vector in ℤ[q]/(q^12+1). -/

noncomputable section
namespace MockThetaAnalytic.ShadowEndpoint

open Complex ShadowReadings ShadowPeriod
open KElimination.MockTheta KElimination.MockThetaShadow
open scoped BigOperators

private def degree24 (m : ℕ) : ℕ := (m*m-1)/24
private def reducedSign (m : ℕ) : ℤ := shadowSign m * (-1)^(degree24 m/12)
private def phaseRow (j : ℕ) : ℤ :=
  ∑ m ∈ Finset.range 144, if degree24 m % 12 = j then reducedSign m else 0

private theorem nome_half24 : integerNome (-1/24)^12 = -1 := by
  unfold integerNome
  rw [← Complex.exp_nat_mul, show ((12:ℕ):ℂ)*((2*Real.pi*I)*(-1/24)) =
      -((Real.pi:ℂ)*I) by ring, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

private theorem nome_power576 : integerNome (-1/576)^24 = integerNome (-1/24) := by
  unfold integerNome
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem reduced_phase (m : ℕ) :
    fktyCuspPhase m = integerNome (-1/576) *
      ((reducedSign m : ℂ) * integerNome (-1/24)^(degree24 m % 12)) := by
  have he : fktyCuspPhase m = (shadowSign m : ℂ)*(integerNome (-1/576))^(m^2) := by
    unfold fktyCuspPhase integerNome
    rw [← Complex.exp_nat_mul]
    push_cast
    congr 2
    ring
  by_cases hm : shadowSign m = 0
  · simp [he, reducedSign, hm]
  have hs : (m*m)%24 = 1 := (square_lattice m).mpr (by
    unfold shadowSign at hm
    split_ifs at hm <;> omega)
  have hd : m^2 = 1+24*degree24 m := by
    unfold degree24
    rw [pow_two]
    omega
  have hr : integerNome (-1/24)^(degree24 m) =
      integerNome (-1/24)^(degree24 m % 12) * (-1:ℂ)^(degree24 m/12) := by
    conv_lhs => rw [← Nat.mod_add_div (degree24 m) 12]
    rw [pow_add, pow_mul, nome_half24]
  rw [he, hd, pow_add, pow_one, pow_mul, nome_power576, hr, reducedSign, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  ring

private theorem phaseRows_eval :
    (∑ m ∈ Finset.range 144, fktyCuspPhase m) =
      integerNome (-1/576) * ∑ j ∈ Finset.range 12, (phaseRow j : ℂ)*integerNome (-1/24)^j := by
  simp_rw [reduced_phase, phaseRow, Int.cast_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range 12)]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.mul_sum, Finset.sum_eq_single (degree24 m % 12)]
  · simp
  · intro j _ h
    simp [Ne.symm h]
  · intro hn
    exact (hn (Finset.mem_range.mpr (Nat.mod_lt _ (by decide)))).elim

private theorem row_table (j : Fin 12) :
    phaseRow j = (![4,-4,4,-4,0,0,4,0,0,4,4,0] : Fin 12 → ℤ) j :=
  (by decide +kernel : ∀ j : Fin 12, phaseRow j = (![4,-4,4,-4,0,0,4,0,0,4,4,0] : Fin 12 → ℤ) j) j

private theorem eval_table (q : ℂ) :
    (∑ j ∈ Finset.range 12, (phaseRow j : ℂ)*q^j) =
      4 - 4*q + 4*q^2 - 4*q^3 + 4*q^6 + 4*q^9 + 4*q^10 := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [row_table]
  norm_num [Fin.sum_univ_succ]
  ring

/-- At the diagonal the full ray period is the normalized finite FKTY value
at the reflected order-24 cusp. -/
theorem fktyCuspPeriod_eq_fktyPhi24 :
    fktyCuspPeriod (-1/24) = fktyPhi (-1/24) := by
  rw [fktyCuspPeriod_cusp, phaseRows_eval, eval_table, fktyPhi,
    show (-1/24 : ℚ).den / 2 = 12 by decide +kernel,
    show ((-1/24 : ℚ) : ℂ) = (-1/24 : ℂ) by norm_num,
    show (-1/24 : ℂ)/24 = -1/576 by ring, fNegPartial_reduced12 _ nome_half24]
  ring

/-- One sign-reversing block of the S6 reconstruction is sufficient at
the diagonal. Wider prefixes give the same exact value. -/
theorem averagedFullPeriod_eq_fktyPhi24 (D : ℕ) (hD : 144 ≤ modeCount D) :
    averagedPeriod (observe D mockCoeff) (fun _ => 1) 144 (-1/24) = fktyPhi (-1/24) := by
  rw [← fktyCuspPeriod_eq_fktyPhi24, fktyCuspPeriod_cusp, averagedFullPeriod_cusp D hD]

end MockThetaAnalytic.ShadowEndpoint
