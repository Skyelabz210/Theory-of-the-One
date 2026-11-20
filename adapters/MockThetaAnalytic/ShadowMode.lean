import ShadowProjection
import MockThetaShadow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The complementary error function and one nonholomorphic Fourier mode of
the integer-exponent completion of Ramanujan's third-order f. The positive
parameter m is the absolute value of a Fourier label and ε supplies its sign. -/

noncomputable section

namespace MockThetaAnalytic

open Complex

/-- The standard complementary error function defined by its Gaussian integral. -/
def erfc (x : ℝ) : ℝ :=
  1 - (2 / Real.sqrt Real.pi) * ∫ t in 0..x, Real.exp (-(t ^ 2))

theorem hasDerivAt_erfc (x : ℝ) :
    HasDerivAt erfc (-(2 / Real.sqrt Real.pi * Real.exp (-(x ^ 2)))) x := by
  have h : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) := by fun_prop
  exact (((h.integral_hasStrictDerivAt 0 x).hasDerivAt.const_mul
    (2 / Real.sqrt Real.pi)).const_sub 1)

private def frequency (m : ℝ) : ℝ := 2 * Real.pi * m ^ 2

/-- The factor multiplying exp(−2πim²z). -/
def modeAmplitude (ε m y : ℝ) : ℝ :=
  -2 * ε * erfc (Real.sqrt (4 * Real.pi * m ^ 2 * y))

private theorem amplitude_derivative (ε m y : ℝ) (hm : 0 < m) (hy : 0 < y) :
    HasDerivAt (modeAmplitude ε m)
      (4 * ε * m * Real.exp (-(2 * frequency m * y)) / Real.sqrt y) y := by
  have hπ := Real.sq_sqrt Real.pi_pos.le
  have hπ' := Real.sqrt_pos.2 Real.pi_pos
  have hys := Real.sq_sqrt hy.le
  have hys' := Real.sqrt_pos.2 hy
  have harg : (2 * m * Real.sqrt Real.pi * Real.sqrt y) ^ 2 = 2 * frequency m * y := by
    simp only [mul_pow, hπ, hys, frequency]
    ring
  have arg_eq (t : ℝ) :
      Real.sqrt (4 * Real.pi * m ^ 2 * t) = 2 * m * Real.sqrt Real.pi * Real.sqrt t := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi * m ^ 2),
      Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_sq hm.le]
    have hfour : Real.sqrt 4 = 2 :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
    rw [hfour]
    ring
  change HasDerivAt (fun t => -2 * ε * erfc (Real.sqrt (4 * Real.pi * m ^ 2 * t))) _ y
  simp only [arg_eq]
  have h := ((hasDerivAt_erfc _).comp y
    ((Real.hasDerivAt_sqrt hy.ne').const_mul (2 * m * Real.sqrt Real.pi))).const_mul (-2 * ε)
  convert h using 1
  rw [harg]
  field_simp [hπ'.ne', hys'.ne']
  ring

/-- The real height derivative of the correction amplitude at a positive label. -/
theorem hasDerivAt_modeAmplitude (ε m y : ℝ) (hm : 0 < m) (hy : 0 < y) :
    HasDerivAt (modeAmplitude ε m)
      (4 * ε * m * Real.exp (-(4 * Real.pi * m ^ 2 * y)) / Real.sqrt y) y := by
  convert amplitude_derivative ε m y hm hy using 1
  unfold frequency
  ring_nf

/-- A real amplitude depending on the height times a holomorphic function.
The complex derivative of the holomorphic factor cancels in ∂/∂z̄. -/
private theorem xiHalf_amplitude_mul {A : ℝ → ℝ} {g : ℂ → ℂ} {z : ℂ} {a : ℝ} {b : ℂ}
    (ha : HasDerivAt A a z.im) (hg : HasDerivAt g b z) :
    xiHalf (fun w : ℂ => (A w.im : ℂ) * g w) z =
      (Real.sqrt z.im * a : ℝ) * (starRingEnd ℂ) (g z) := by
  have ha' := Complex.ofRealCLM.hasFDerivAt.comp z
    (ha.comp_hasFDerivAt z Complex.imCLM.hasFDerivAt)
  have hd : fderiv ℝ (fun w : ℂ => (A w.im : ℂ) * g w) z =
      ((A z.im : ℂ) • (b • (1 : ℂ →L[ℝ] ℂ)) + g z • ofRealCLM.comp (a • imCLM)) :=
    (ha'.mul hg.complexToReal_fderiv).fderiv
  let h := fun w : ℂ => (A w.im : ℂ) * g w
  have hwir : (fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2 = I * a * g z / 2 := by
    dsimp only [h]
    rw [hd]
    simp [Function.comp_def, Complex.real_smul, smul_eq_mul]
    ring_nf
    simp [Complex.I_sq]
  change 2 * I * (Real.sqrt z.im : ℂ) * (starRingEnd ℂ) _ = _
  rw [hwir]
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ _
  simp [htwo]
  ring_nf
  simp [Complex.I_sq]

/-- One signed mode with positive absolute Fourier label m. -/
def nonholomorphicMode (ε m : ℝ) (z : ℂ) : ℂ :=
  (modeAmplitude ε m z.im : ℂ) * Complex.exp (-(frequency m : ℂ) * I * z)

theorem xiHalf_nonholomorphicMode (ε m : ℝ) (hm : 0 < m) (z : ℂ) (hy : 0 < z.im) :
    xiHalf (nonholomorphicMode ε m) z =
      (4 * ε * m : ℝ) * Complex.exp ((2 * Real.pi * m ^ 2 : ℝ) * I * z) := by
  have hg : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-(frequency m : ℂ) * I * w)) z := by
    fun_prop
  have hw := xiHalf_amplitude_mul (amplitude_derivative ε m z.im hm hy) hg.hasDerivAt
  change xiHalf (fun w : ℂ => (modeAmplitude ε m w.im : ℂ) * _) z = _
  rw [hw]
  have hs : Real.sqrt z.im * (4 * ε * m * Real.exp (-(2 * frequency m * z.im)) / Real.sqrt z.im) =
      (4 * ε * m) * Real.exp (-(2 * frequency m * z.im)) := by
    field_simp [(Real.sqrt_pos.2 hy).ne']
  rw [hs, Complex.ofReal_mul, Complex.ofReal_exp,
    ← Complex.exp_conj]
  change _ = (4 * ε * m : ℝ) * Complex.exp ((frequency m : ℂ) * I * z)
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  apply Complex.ext
  all_goals simp [Complex.mul_re, Complex.mul_im]
  ring


open KElimination.MockThetaShadow

/-- The first D coefficients of the integer-scaled holomorphic part
Q⁻¹f(Q²⁴) with Q = exp(2πiz). The degree at d = 0 is −1. -/
def finiteHolomorphicPart (D : ℕ) (z : ℂ) : ℂ :=
  ∑ d ∈ Finset.range D, ((KElimination.MockTheta.mockCoeff d : ℤ) : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * I * (normalizedExponent d : ℂ) * z)

/-- Retain the first D mock coefficients and the Fourier modes with positive
absolute labels m ≤ M in the nonholomorphic part. -/
def finiteCompletion (D M : ℕ) (z : ℂ) : ℂ :=
  finiteHolomorphicPart D z +
    ∑ m ∈ Finset.Icc 1 M, nonholomorphicMode (shadowSign m : ℝ) m z

/-- The actual ξ derivative of the finite completion gives the corresponding
truncation of the primitive unary theta series with multiplier four. -/
theorem xiHalf_finiteCompletion (D M : ℕ) (z : ℂ) (hy : 0 < z.im) :
    xiHalf (finiteCompletion D M) z =
      4 * ∑ m ∈ Finset.Icc 1 M, (shadowWeight m : ℂ) *
        Complex.exp ((2 * Real.pi * (m : ℝ) ^ 2 : ℝ) * I * z) := by
  have hhol : DifferentiableAt ℂ (finiteHolomorphicPart D) z := by
    unfold finiteHolomorphicPart
    fun_prop
  have hzero : xiHalf (finiteHolomorphicPart D) z = 0 := by
    simpa using xiHalf_amplitude_mul (hasDerivAt_const z.im (1 : ℝ)) hhol.hasDerivAt
  have pos (m : ℕ) (h : m ∈ Finset.Icc 1 M) : 0 < (m : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp h).1
  have hdiff (m : ℕ) (hm : m ∈ Finset.Icc 1 M) :
      DifferentiableAt ℝ (nonholomorphicMode (shadowSign m : ℝ) m) z := by
    have ha := amplitude_derivative (shadowSign m : ℝ) m z.im (pos m hm) hy
    have hA := Complex.ofRealCLM.hasFDerivAt.comp z
      (ha.comp_hasFDerivAt z Complex.imCLM.hasFDerivAt)
    have hg : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-(frequency m : ℂ) * I * w)) z := by
      fun_prop
    exact hA.differentiableAt.mul (hg.restrictScalars ℝ)
  unfold finiteCompletion
  rw [xiHalf_add _ _ _ (hhol.restrictScalars ℝ) (DifferentiableAt.fun_sum hdiff),
    hzero, zero_add, xiHalf_sum _ _ _ hdiff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [xiHalf_nonholomorphicMode _ _ (pos m hm) z hy]
  unfold shadowWeight
  push_cast
  ring


open Filter KElimination.ShadowConvergence
open scoped Topology

/-- The ξ-images of the actual finite completions converge to the full unary
shadow on the upper half-plane. The holomorphic truncation may vary freely. -/
theorem tendsto_xiHalf_finiteCompletion (D : ℕ → ℕ) (z : ℂ) (hy : 0 < z.im) :
    Tendsto (fun M => xiHalf (finiteCompletion (D M) M) z) atTop
      (𝓝 (4 * shadowSeries (integerNome z))) := by
  have hzero : shadowTerm (integerNome z) 0 = 0 := by
    simp [shadowTerm, shadowWeight]
  have hpartial (M : ℕ) : xiHalf (finiteCompletion (D M) M) z =
      4 * ∑ m ∈ Finset.range (M + 1), shadowTerm (integerNome z) m := by
    rw [xiHalf_finiteCompletion _ _ _ hy]
    have hset : Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert (by simp), hzero, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    unfold shadowTerm integerNome
    rw [← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  simp_rw [hpartial]
  have hsum := (shadowTerm_summable _ (norm_integerNome_lt_one z hy)).hasSum.tendsto_sum_nat
  exact tendsto_const_nhds.mul (hsum.comp (tendsto_add_atTop_nat 1))

end MockThetaAnalytic
