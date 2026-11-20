import ShadowOperator
import ShadowConvergence
import Mathlib.Tactic.Ring

/-! Horizontal translation by j/11 multiplies a mode of signed integral
Fourier exponent k by the standard additive character at k*j. Orthogonality
therefore selects the exponent class in the integer-scaled unary theta series. -/

noncomputable section

namespace MockThetaAnalytic

open Complex KElimination.ShadowConvergence
open scoped BigOperators

/-- The nome for integral Fourier exponents in the rescaled variable z. -/
def integerNome (z : ℂ) : ℂ := exp (2 * (Real.pi : ℂ) * I * z)

theorem integerNome_eq_shadowNome (z : ℂ) : integerNome z = shadowNome (24*z) := by
  unfold integerNome shadowNome
  push_cast
  congr 1
  ring

theorem norm_integerNome_lt_one (z : ℂ) (hz : 0 < z.im) : ‖integerNome z‖ < 1 := by
  rw [integerNome_eq_shadowNome]
  apply norm_shadowNome_lt_one
  simpa [Complex.mul_im] using (mul_pos (by norm_num : (0 : ℝ) < 24) hz)

private theorem translated_mode (k : ℤ) (z : ℂ) (j : ZMod 11) :
    integerNome (z + (shift11 j : ℂ)) ^ k =
      ZMod.stdAddChar ((k : ZMod 11)*j) * integerNome z ^ k := by
  have hj : ((k * (j.val : ℤ) : ℤ) : ZMod 11) = (k : ZMod 11)*j := by
    simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← hj, ZMod.stdAddChar_coe]
  simp only [integerNome, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  unfold shift11
  push_cast
  ring

private theorem frequencySum (t : ZMod 11) :
    (∑ j : ZMod 11, ZMod.stdAddChar (t*j)) = if t = 0 then (11 : ℂ) else 0 := by
  split_ifs with h
  · simp only [h, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one, Nat.cast_ofNat]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 11 h)

/-- On a Laurent monomial the projector is exactly the indicator of k mod 11. -/
theorem project11_monomial (r : ZMod 11) (k : ℤ) (z : ℂ) :
    project11 r (fun w => integerNome w ^ k) z =
      if (k : ZMod 11) = r then integerNome z ^ k else 0 := by
  calc
    _ = (∑ j : ZMod 11, ZMod.stdAddChar (((k : ZMod 11)-r)*j)) *
        (integerNome z ^ k / 11) := by
      rw [Finset.sum_mul]
      unfold project11
      apply Finset.sum_congr rfl
      intro j _
      dsimp only
      rw [translated_mode, show ((k : ZMod 11)-r)*j = -(r*j) + (k : ZMod 11)*j by ring,
        AddChar.map_add_eq_mul]
      ring
    _ = _ := by
      rw [frequencySum]
      by_cases h : (k : ZMod 11) = r
      · simp [h]
        ring
      · simp [h, sub_eq_zero]

theorem project11_const_mul (r : ZMod 11) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    project11 r (fun w => c * f w) z = c * project11 r f z := by
  unfold project11
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem project11_tsum (r : ZMod 11) (F : ℕ → ℂ → ℂ) (z : ℂ)
    (hs : ∀ j : ZMod 11, Summable (fun m => F m (z + (shift11 j : ℂ)))) :
    project11 r (fun w => ∑' m, F m w) z = ∑' m, project11 r (F m) z := by
  unfold project11
  rw [Summable.tsum_finsetSum (fun j _ => (hs j).mul_left (ZMod.stdAddChar (-(r*j)) / 11))]
  apply Finset.sum_congr rfl
  intro j _
  exact ((hs j).tsum_mul_left _).symm

private theorem exponentClass (m : ℕ) (r : Fin 11) :
    ((m^2 : ℕ) : ZMod 11) = (r.val : ZMod 11) ↔ degreeClass m = r := by
  apply Iff.trans (ZMod.val_injective 11).eq_iff.symm
  rw [ZMod.val_natCast, ZMod.val_natCast_of_lt r.isLt, Fin.ext_iff]
  rfl

/-- For Im z > 0, the translation projector applied to the actual convergent
unary series keeps precisely the modes whose square exponent belongs to r. -/
theorem project11_shadowSeries (r : Fin 11) (z : ℂ) (hz : 0 < z.im) :
    project11 (r.val : ZMod 11) (fun w => shadowSeries (integerNome w)) z =
      shadowDegreeBin r (integerNome z) := by
  change project11 _ (fun w => ∑' m, shadowTerm (integerNome w) m) z = _
  rw [project11_tsum _ (fun m w => shadowTerm (integerNome w) m) z (fun j =>
    shadowTerm_summable _ (norm_integerNome_lt_one _ (by simpa using hz)))]
  unfold shadowDegreeBin
  apply tsum_congr
  intro m
  have hm := project11_monomial (r.val : ZMod 11) ((m^2 : ℕ) : ℤ) z
  simp only [zpow_natCast, Int.cast_natCast] at hm
  unfold shadowTerm
  rw [project11_const_mul, hm]
  by_cases h : degreeClass m = r
  · rw [if_pos ((exponentClass m r).mpr h), if_pos h]
  · rw [if_neg (mt (exponentClass m r).mp h), if_neg h, mul_zero]

/-- The published ξ normalization multiplies every degree bin by four. -/
theorem project11_xiShadowSeries (r : Fin 11) (z : ℂ) (hz : 0 < z.im) :
    project11 (r.val : ZMod 11) (fun w => 4 * shadowSeries (integerNome w)) z =
      4 * shadowDegreeBin r (integerNome z) := by
  rw [project11_const_mul, project11_shadowSeries r z hz]

/-- Given the published ξ identity for a completion H at the eleven translates,
the ξ image of its r-projection is four times the actual unary bin at −r. -/
theorem xiHalf_project11_of_shadow (r : ZMod 11) (H : ℂ → ℂ) (z : ℂ) (hz : 0 < z.im)
    (hd : ∀ j, DifferentiableAt ℝ H (z + (shift11 j : ℂ)))
    (hξ : ∀ j, xiHalf H (z + (shift11 j : ℂ)) =
      4 * shadowSeries (integerNome (z + (shift11 j : ℂ)))) :
    xiHalf (project11 r H) z =
      4 * shadowDegreeBin ⟨(-r).val, (-r).val_lt⟩ (integerNome z) := by
  rw [xiHalf_project11 r H z hd]
  calc
    _ = project11 (-r) (fun w => 4 * shadowSeries (integerNome w)) z := by
      unfold project11
      apply Finset.sum_congr rfl
      intro j _
      rw [hξ]
    _ = _ := by
      simpa only [ZMod.natCast_zmod_val] using
        project11_xiShadowSeries ⟨(-r).val, (-r).val_lt⟩ z hz

end MockThetaAnalytic
