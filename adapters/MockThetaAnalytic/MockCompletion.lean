import MockHolomorphic
import ShadowInfinite
import ShadowSectors

/-! The explicit Fourier completion of Ramanujan's third-order f and its
differential shadow above the real axis, with exact support modulo eleven.
The transformation law of the completed vector is due to Zwegers. -/

noncomputable section

namespace MockThetaAnalytic

open Complex KElimination.ShadowConvergence

/-- The integer-scaled holomorphic part Q⁻¹ f(Q²⁴), Q = exp(2πiz),
plus the signed nonholomorphic Fourier correction. -/
def mockCompletion (z : ℂ) : ℂ := normalizedF z + nonholomorphicPart z

theorem differentiableAt_mockCompletion (z : ℂ) (hz : 0 < z.im) :
    DifferentiableAt ℝ mockCompletion z :=
  ((differentiableAt_normalizedF z hz).restrictScalars ℝ).add
    (differentiableAt_nonholomorphicPart z hz)

/-- The antiholomorphic derivative annihilates a holomorphic part. -/
theorem xiHalf_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    xiHalf f z = 0 := by
  rw [xiHalf, hf.hasDerivAt.complexToReal_fderiv.fderiv]
  simp [smul_eq_mul]
  right
  ring_nf
  simp [Complex.I_sq]

/-- Differentiating the full convergent Fourier completion gives four times
the primitive, integrally normalized unary theta series. -/
theorem xiHalf_mockCompletion (z : ℂ) (hz : 0 < z.im) :
    xiHalf mockCompletion z = 4 * shadowSeries (integerNome z) := by
  unfold mockCompletion
  rw [xiHalf_add _ _ _ ((differentiableAt_normalizedF z hz).restrictScalars ℝ)
    (differentiableAt_nonholomorphicPart z hz),
    xiHalf_eq_zero_of_differentiableAt (differentiableAt_normalizedF z hz),
    zero_add, xiHalf_nonholomorphicPart z hz]

/-- On a completion projected to class r, conjugation selects the unary
Fourier series in class −r. All eleven translations preserve the height. -/
theorem xiHalf_project11_mockCompletion (r : ZMod 11) (z : ℂ) (hz : 0 < z.im) :
    xiHalf (project11 r mockCompletion) z =
      4 * shadowDegreeBin ⟨(-r).val, (-r).val_lt⟩ (integerNome z) :=
  xiHalf_project11_of_shadow r mockCompletion z hz
    (fun _ => differentiableAt_mockCompletion _ (by simpa using hz))
    (fun _ => xiHalf_mockCompletion _ (by simpa using hz))

/-- Exactly five completion projections have identically vanishing shadow.
For every other class the projected shadow takes a nonzero value somewhere
on the upper half-plane. -/
theorem xiHalf_project11_mockCompletion_eq_zero_iff (r : ZMod 11) :
    (∀ z : ℂ, 0 < z.im → xiHalf (project11 r mockCompletion) z = 0) ↔
      r.val ∈ ([1, 3, 4, 5, 9] : List ℕ) := by
  have h (s : ZMod 11) : (-s).val ∉ ([0, 1, 3, 4, 5, 9] : List ℕ) ↔
      s.val ∈ ([1, 3, 4, 5, 9] : List ℕ) := by decide +revert
  rw [← h, ← shadowDegreeBin_identically_zero_iff ⟨(-r).val, (-r).val_lt⟩]
  apply forall_congr'
  intro z
  apply forall_congr'
  intro hz
  rw [xiHalf_project11_mockCompletion r z hz]
  simp

end MockThetaAnalytic
