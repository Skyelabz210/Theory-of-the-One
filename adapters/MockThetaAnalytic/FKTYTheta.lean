import MockCompletion
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Folsom–Ki–Truong Vu–Yang, equation (3.12), at (a,b,c)=(1,2,0).
The series is indexed by all integers, with the Kronecker character (12/n).
Pairing the positive and negative labels relates its normalization to ξ of
the completed third-order f. -/

noncomputable section

namespace MockThetaAnalytic

open KElimination.MockThetaShadow KElimination.ShadowConvergence

/-- The residue table of the Kronecker character (12/n). -/
def fktyChi12 (n : ℤ) : ℤ :=
  if n % 12 = 1 ∨ n % 12 = 11 then 1
  else if n % 12 = 5 ∨ n % 12 = 7 then -1 else 0

theorem fktyChi12_period (n : ℤ) : fktyChi12 (n + 12) = fktyChi12 n := by
  simp [fktyChi12]

/-- The odd labels carry (-1)^((n-1)/2). The character kills all even labels.
The nome is e(u/24) and the degree is the ordinary integral square. -/
def fktyThetaTerm (u : ℂ) (n : ℤ) : ℂ :=
  (n : ℂ) * (fktyChi12 n : ℂ) * (-1 : ℂ) ^ ((n - 1) / 2) *
    shadowNome u ^ (n.natAbs ^ 2)

def fktyTheta (u : ℂ) : ℂ := ∑' n : ℤ, fktyThetaTerm u n

/-- Write the nome power as the exponential with the signed index in (3.12). -/
theorem fktyThetaTerm_eq_exp (u : ℂ) (n : ℤ) :
    fktyThetaTerm u n = (n : ℂ) * (fktyChi12 n : ℂ) * (-1 : ℂ) ^ ((n - 1) / 2) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * u / 24) := by
  have h : (n.natAbs : ℂ) ^ 2 = (n : ℂ) ^ 2 := by
    have hs : (n.natAbs : ℤ) ^ 2 = n ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
    simpa only [Int.cast_pow, Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℂ)) hs
  rw [fktyThetaTerm, shadowNome, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  rw [h]
  ring

private def signedResidue (n : ℤ) : ℤ :=
  if n % 6 = 1 then 1 else if n % 6 = 5 then -1 else 0

private theorem character_product (n : ℤ) :
    (fktyChi12 n : ℂ) * (-1 : ℂ) ^ ((n - 1) / 2) = (signedResidue n : ℂ) := by
  simp only [neg_one_zpow_eq_ite, Int.even_iff]
  unfold fktyChi12 signedResidue
  split_ifs <;> norm_num <;> omega

private theorem signedResidue_neg (n : ℤ) : signedResidue (-n) = -signedResidue n := by
  unfold signedResidue
  split_ifs <;> norm_num <;> omega

private theorem signedResidue_nat (m : ℕ) : signedResidue m = shadowSign m := by
  have hm : (m : ℤ) % 6 = ((m % 6 : ℕ) : ℤ) := (Int.natCast_mod m 6).symm
  simp only [signedResidue, shadowSign, hm]
  split_ifs <;> omega

private theorem term_nat (u : ℂ) (m : ℕ) :
    fktyThetaTerm u m = shadowTerm (shadowNome u) m := by
  rw [fktyThetaTerm, mul_assoc _ (fktyChi12 _ : ℂ) _, character_product, signedResidue_nat]
  simp [shadowTerm, shadowWeight, mul_comm]

private theorem term_neg_nat (u : ℂ) (m : ℕ) :
    fktyThetaTerm u (-(m : ℤ)) = shadowTerm (shadowNome u) m := by
  unfold fktyThetaTerm
  rw [mul_assoc _ (fktyChi12 _ : ℂ) _, character_product, signedResidue_neg, signedResidue_nat]
  simp [shadowTerm, shadowWeight, mul_comm]

theorem fktyThetaTerm_summable (u : ℂ) (hu : 0 < u.im) : Summable (fktyThetaTerm u) := by
  have hs := shadowTerm_summable _ (norm_shadowNome_lt_one u hu)
  apply Summable.of_nat_of_neg
  · simpa only [term_nat] using hs
  · simpa only [term_neg_nat] using hs

/-- The two halves of the bilateral theta series have equal terms and the
zero coefficient vanishes, producing the factor two. -/
theorem fktyTheta_eq_shadowSeries (u : ℂ) (hu : 0 < u.im) :
    fktyTheta u = 2 * shadowSeries (shadowNome u) := by
  have h := shadowTerm_summable _ (norm_shadowNome_lt_one u hu)
  have hp : Summable (fun n : ℕ => fktyThetaTerm u n) := by simpa only [term_nat] using h
  have hn : Summable (fun n : ℕ => fktyThetaTerm u (-(n : ℤ))) := by
    simpa only [term_neg_nat] using h
  rw [fktyTheta, hp.tsum_of_nat_of_neg hn]
  have hz : fktyThetaTerm u 0 = 0 := by simp [fktyThetaTerm]
  simp only [term_nat, term_neg_nat, hz, shadowSeries, two_mul, sub_zero]

/-- In the coordinates of the completed third-order f, the period kernel is
exactly one half of its differential shadow evaluated at u/24. -/
theorem fktyTheta_eq_xiHalf (u : ℂ) (hu : 0 < u.im) :
    fktyTheta u = xiHalf mockCompletion (u / 24) / 2 := by
  have hy : 0 < (u / 24).im := by rw [Complex.div_ofNat_im]; positivity
  rw [xiHalf_mockCompletion _ hy, integerNome_eq_shadowNome, fktyTheta_eq_shadowSeries u hu]
  rw [show 24 * (u / 24) = u by ring]
  ring

end MockThetaAnalytic
