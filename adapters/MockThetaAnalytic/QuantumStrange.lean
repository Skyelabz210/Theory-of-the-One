import QuantumRadial
import ShadowProjection
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! Bryson–Ono–Pitman–Rhoades (2012), Theorem 1.3, give a weight-3/2
quantum modular form whose rational cusp values are e(−x/24) U(1;e(x))
in the notation of Folsom–Ono–Rhoades. BOPR put a minus on the elliptic
variable in their Pochhammer symbols, so their specialization is U(−1;q).
Here e(x) = exp(2πix). We prove termination, denominator independence, the
translation law, and explicit cusp values at 1/2 and 1/11. The inversion law is in BOPR. -/

noncomputable section

namespace MockThetaAnalytic

open Complex KElimination.QuantumRadial KElimination.ResidueSeries

/-- The factor 1−ζ^K in (ζ;ζ)_n kills every term from n=K onwards. -/
theorem pochhammer_self_eq_zero {ζ : ℂ} {K n : ℕ} (hK : 0 < K)
    (hζ : ζ^K = 1) (hn : K ≤ n) : pochhammer ζ ζ n = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [pochhammer]
    by_cases h : K ≤ n
    · rw [ih h, zero_mul]
    · have hKn : n+1 = K := by omega
      rw [mul_comm ζ (ζ^n), ← pow_succ, hKn, hζ, sub_self, mul_zero]

/-- The first K terms give the value of U(1;ζ) at any K-th root. -/
theorem uOnePartial_stable {ζ : ℂ} {K N : ℕ} (hK : 0 < K)
    (hζ : ζ^K = 1) (hN : K ≤ N) :
    uTwoPartial N 1 1 ζ = uTwoPartial K 1 1 ζ := by
  apply sumBelow_eq_of_tail_zero _ _ _ hN
  intro n hn _
  simp only [one_mul, pochhammer_self_eq_zero hK hζ hn, zero_mul]

/-- The numerical series defining U(1;ζ) is summable at a root because its
terms eventually vanish. Its sum is the finite core polynomial. -/
theorem hasSum_uOne {ζ : ℂ} {K : ℕ} (hK : 0 < K) (hζ : ζ^K = 1) :
    HasSum (fun n : ℕ => pochhammer ζ ζ n ^ 2 * ζ^(n+1)) (uTwoPartial K 1 1 ζ) := by
  have hsum (N : ℕ) :
      uTwoPartial N 1 1 ζ = ∑ n ∈ Finset.range N, pochhammer ζ ζ n ^ 2 * ζ^(n+1) := by
    induction N with
    | zero => simp [uTwoPartial, sumBelow]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp [uTwoPartial, sumBelow, pow_two]
  rw [hsum]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  rw [pochhammer_self_eq_zero hK hζ (by simpa using hn)]
  simp

/-- The exponential closing relation holds for every representation a/K,
even when a and K have a common factor. -/
theorem integerNome_fraction_pow (a : ℤ) (K : ℕ) (hK : 0 < K) :
    integerNome ((a : ℂ) / K) ^ K = 1 := by
  rw [integerNome, ← Complex.exp_nat_mul]
  convert Complex.exp_int_mul_two_pi_mul_I a using 2
  have hn : (K : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  field_simp

private theorem integerNome_den_pow (x : ℚ) : integerNome (x : ℂ)^x.den = 1 := by
  rw [Rat.cast_def]
  exact integerNome_fraction_pow x.num x.den x.den_pos

/-- Normalized finite sample at a rational x, using its canonical denominator.
The formula defines a value at zero as well; BOPR's inversion law is stated
on nonzero rational cusps. -/
def strangeCusp (x : ℚ) : ℂ :=
  integerNome (-(x : ℂ)/24) * uTwoPartial x.den 1 1 (integerNome (x : ℂ))

/-- Identification with the normalized, terminating series at the rational cusp.
This evaluates at the cusp itself and uses no limiting radial process. -/
theorem strangeCusp_eq_tsum (x : ℚ) :
    strangeCusp x = integerNome (-(x : ℂ)/24) *
      ∑' n : ℕ, pochhammer (integerNome x) (integerNome x) n ^ 2 * integerNome x ^ (n+1) := by
  rw [(hasSum_uOne x.den_pos (integerNome_den_pow x)).tsum_eq]
  rfl

/-- Evaluating with any other denominator K and any cutoff N≥K gives the
same sample; no reduction of the supplied fraction is required. -/
theorem strangeCusp_eq_partial (x : ℚ) (a : ℤ) (K N : ℕ) (hK : 0 < K)
    (hx : x = (a : ℚ)/K) (hN : K ≤ N) :
    strangeCusp x = integerNome (-(x : ℂ)/24) * uTwoPartial N 1 1 (integerNome (x : ℂ)) := by
  have hxC : (x : ℂ) = (a : ℂ)/K := by exact_mod_cast hx
  have hzK : integerNome (x : ℂ)^K = 1 := hxC ▸ integerNome_fraction_pow a K hK
  have h₁ := uOnePartial_stable x.den_pos (integerNome_den_pow x) (Nat.le_max_left x.den N)
  have h₂ := uOnePartial_stable hK hzK (hN.trans (Nat.le_max_right x.den N))
  have h₃ := uOnePartial_stable hK hzK hN
  exact congrArg (integerNome (-(x : ℂ)/24) * ·) (h₁.symm.trans (h₂.trans h₃.symm))

private theorem integerNome_add (x y : ℂ) : integerNome (x+y) = integerNome x * integerNome y := by
  rw [integerNome, mul_add, Complex.exp_add]
  rfl

/-- The T transformation of the normalized rational cusp samples. -/
theorem strangeCusp_add_one (x : ℚ) :
    strangeCusp (x+1) = integerNome (-1/24) * strangeCusp x := by
  have hd : (x+1).den = x.den := Rat.add_intCast_den x 1
  simp only [strangeCusp, hd, Rat.cast_add, Rat.cast_one]
  rw [show -((x : ℂ)+1)/24 = -1/24 + (-(x : ℂ)/24) by ring, integerNome_add,
    integerNome_add, show integerNome 1 = 1 by simp [integerNome], mul_one, mul_assoc]

/-- At x=1/2 the nome is −1 and the two terms in U(1;−1) sum to 3. -/
theorem strangeCusp_half : strangeCusp (1/2) = 3 * integerNome (-1/48) := by
  have h := strangeCusp_eq_partial (1/2) 1 2 2 (by decide) (by norm_num) (le_refl _)
  have hζ : integerNome (1/2) = -1 := by
    rw [integerNome, show 2 * (Real.pi : ℂ) * I * (1/2) = (Real.pi : ℂ) * I by ring,
      Complex.exp_pi_mul_I]
  rw [h]
  push_cast
  rw [hζ]
  norm_num [uTwoPartial, sumBelow, pochhammer]
  ring

/-- The polynomial representing the order-eleven value in the standard
basis 1,q,…,q⁹ of the eleventh cyclotomic field. -/
def strangePolynomial11 (q : ℂ) : ℂ :=
  43 + 22*q + 22*q^2 + 22*q^3 + 31*q^4 + 22*q^5 + 33*q^6 + 19*q^7 + 22*q^8 + 7*q^9

/-- Reduction of the eleven terminating summands at any primitive eleventh root. -/
theorem strangeValue_eleven (q : ℂ) (hq : IsPrimitiveRoot q 11) :
    uTwoPartial 11 1 1 q = strangePolynomial11 q := by
  have h := hq.geom_sum_eq_zero (by decide : 1 < 11)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, zero_add] at h
  simp only [strangePolynomial11, uTwoPartial, sumBelow, pochhammer, one_mul, pow_zero, pow_one]
  grind (splits := 0) only

/-- The normalized sample at 1/11 includes the twist e(−1/264). -/
theorem strangeCusp_eleventh :
    strangeCusp (1/11) = integerNome (-1/264) * strangePolynomial11 (integerNome (1/11)) := by
  have h := strangeCusp_eq_partial (1/11) 1 11 11 (by decide) (by norm_num) (le_refl _)
  have hz : IsPrimitiveRoot (integerNome (1/11)) 11 := by
    simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 11 (by decide)
  rw [h]
  push_cast
  rw [strangeValue_eleven _ hz]
  norm_num

end MockThetaAnalytic
